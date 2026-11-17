// Optimized, fault-based evidence of unconditional loads, including misses
// and nonwinning buckets. No speculative prefetch counts as a required read.
// The value-plane kernels (ExtractValueRange, ValueAccumulator, ExtractMeta)
// and the value-worker pool must read every value line of a probed bucket
// whether or not it holds the winning entry (`take` = 0 or 1), so the memory
// trace does not depend on where, or whether, the key was found.  The last
// required line is placed against a PROT_NONE page and each case runs in a
// forked child: a SIGSEGV proves the load was issued even in an optimized
// build, where a compiler could otherwise elide it.
#include "src/oram/levelarena/cpu_byteslice_level_arena_value_workers.hpp"
#include <cstdio>
#include <cstring>
#include <stdexcept>
#if defined(__unix__)
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <unistd.h>
#include <signal.h>
#if defined(__linux__)
#include <sys/prctl.h>
#endif
#endif
namespace bs = microram::byteslice;
namespace la = bs::levelarena;
extern "C" __attribute__((noipa)) void ValueMemoryPermute(const uint8_t* bucket,
    size_t begin, size_t width, unsigned slot, uint64_t take, uint8_t* out) {
  uint8_t scratch[256];
  bs::ExtractValueRange(bucket,8,begin,begin+width,slot,scratch);
  microram::core::obliAssignBytes(out,scratch,width,take);
}
extern "C" __attribute__((noipa)) void ValueMemoryAccumulate(const uint8_t* bucket,
    size_t begin, size_t width, unsigned slot, uint64_t take, uint8_t* out) {
  // Same 24-line tiles, with every tile unconditional. Real pool ranges over
  // 24 use permute; this wrapper also checks the primitive's wide composition.
  size_t l = 0;
  for (; l + 24 <= width; l += 24) {
    bs::ValueAccumulator<24> a; a.Blend(bucket+(8+begin+l)*64,take); a.Finish(slot,out+l);
  }
  for (; l < width; ++l) {
    bs::ValueAccumulator<1> a; a.Blend(bucket+(8+begin+l)*64,take); a.Finish(slot,out+l);
  }
}
extern "C" __attribute__((noipa)) uint8_t ValueMemoryMeta(const uint8_t* bucket,
                                                        size_t width, uint64_t match) {
  return bs::ExtractMeta(bucket,bs::Layout{8,width+1,0},match);
}
#if defined(__unix__)
void Expect(bool v,const char* why) { if (!v) throw std::runtime_error(why); }
template <class Fn> void Child(Fn fn,bool fault) {
  const pid_t pid = fork(); Expect(pid >= 0,"fork");
  if (!pid) {
    rlimit lim{0,0}; setrlimit(RLIMIT_CORE,&lim);
#if defined(__linux__)
    // Piped crash collectors ignore RLIMIT_CORE. These faults are expected;
    // suppress collection while preserving the signal observed by waitpid.
    Expect(prctl(PR_SET_DUMPABLE,0) == 0,"disable crash collection");
#endif
    // The expected fault must reach waitpid as SIGSEGV, also when a sanitizer
    // runtime has installed its own handler.
    signal(SIGSEGV, SIG_DFL);
    alarm(5); fn(); _exit(0);
  }
  int status; Expect(waitpid(pid,&status,0) == pid,"waitpid");
  Expect(fault ? WIFSIGNALED(status) && WTERMSIG(status) == SIGSEGV :
      WIFEXITED(status) && WEXITSTATUS(status) == 0,"value line load contract");
}
void Worker(const uint8_t* bucket,size_t width,bs::ValueKernel kernel,bool earlier) {
  la::ValueWorkerPool::Config c; c.workers = 1; c.kernel = kernel;
  const bs::Layout layout{8,width+1,0};
  auto aes = bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(microram::crypto::SecretKeySeed::Fixed(1)));
  la::ValueWorkerPool pool(c,layout,*aes,2,0);
  auto safe = bs::AllocateAligned64(layout.BucketBytes());
  std::memset(safe.get(),0x37,layout.BucketBytes());
  bs::ProbePlan p; p.first_live=0; p.tables.resize(2);
  p.tables[0].kind=bs::TableKind::kDense; p.tables[0].data=safe.get(); p.tables[0].num_buckets=1;
  p.tables[1].kind=bs::TableKind::kDense; p.tables[1].data=const_cast<uint8_t*>(bucket); p.tables[1].num_buckets=1;
  uint8_t out[256]{};
  pool.Begin(&p,{},0,2,nullptr,0,nullptr);
  // earlier winner means this bucket has take zero; miss also has take zero.
  pool.Publish(2,earlier,0,0,23,true);
  pool.Finish(out,1);
}
#endif
int main() {
#if defined(__unix__)
  try {
    const size_t page = sysconf(_SC_PAGESIZE), readable = 5*page;
    auto* data = static_cast<uint8_t*>(mmap(nullptr,readable+page,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0));
    Expect(data != MAP_FAILED,"mmap"); std::memset(data,0xA5,readable);
    Expect(mprotect(data+readable,page,PROT_NONE)==0,"mprotect");
    size_t checks = 0;
    for (size_t width : {1,2,7,8,9,16,33,48,64,100,128,256}) {
      for (size_t guard = 0; guard <= width; ++guard)
        for (size_t begin : {0,3})
          for (uint64_t take : {0,1})
            for (auto kernel : {ValueMemoryPermute,ValueMemoryAccumulate}) {
              const uint8_t* bucket=data+readable-(8+begin+guard)*64;
              Child([&] { uint8_t out[256]{}; kernel(bucket,begin,width,37,take,out); },guard<width);
              ++checks;
            }
      for (uint64_t match : {uint64_t{0},uint64_t{1}<<63}) {
        const uint8_t* bucket=data+readable-(8+width)*64;
        Child([&] { volatile auto m=ValueMemoryMeta(bucket,width,match); (void)m; },true);
      }
      for (auto kernel : {bs::ValueKernel::kAccumulate,bs::ValueKernel::kPermute})
        for (bool earlier : {false,true})
          for (size_t guard : {size_t{0},width/2,width-1,width}) {
            const uint8_t* bucket=data+readable-(8+guard)*64;
            Child([&] { Worker(bucket,width,kernel,earlier); },guard<width);
            ++checks;
          }
    }
    munmap(data,readable+page);
    std::printf("value memory: %zu guarded plane/worker cases passed; meta misses fault\n",checks);
  } catch(const std::exception& e) { std::fprintf(stderr,"value memory: %s\n",e.what()); return 1; }
#else
  std::puts("value memory: unavailable (requires POSIX)");
#endif
}
