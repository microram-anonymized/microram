#pragma once

// Identical benchmark instances side by side, one process per CPU, so a kernel
// is measured while its neighbours compete for the same memory bandwidth (a
// running system rebuilds several levels at once).  Each instance is a forked
// child pinned to its CPU.  The instances meet at a spinning barrier in shared
// memory before every timed region, so those regions start together; an
// instance that finishes early spins at the next barrier and touches no memory.
// Header-only and free of project includes: the baseline builds use it too.
#include <sched.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <atomic>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <functional>
#include <new>
#include <stdexcept>
#include <string>
#include <vector>

namespace benchmark_support {

class ParallelInstances {
 public:
  // "3", "1,2,3" or "1-4,9": one instance per listed CPU, in that order.
  // Empty: one unpinned instance.
  static std::vector<int> ParseCpus(const std::string& list) {
    std::vector<int> cpus;
    size_t begin = 0;
    while (begin < list.size()) {
      const size_t end = std::min(list.find(',', begin), list.size());
      const std::string part = list.substr(begin, end - begin);
      const size_t dash = part.find('-');
      const int first = std::stoi(part.substr(0, dash));
      const int last = dash == std::string::npos ? first : std::stoi(part.substr(dash + 1));
      if (first < 0 || last < first) throw std::invalid_argument("malformed CPU list " + list);
      for (int c = first; c <= last; ++c) cpus.push_back(c);
      begin = end + 1;
    }
    return cpus;
  }

  // Runs `body` in one child per CPU (a single unpinned child for an empty
  // list) and waits for all of them.  Returns 0 if every child returned 0,
  // otherwise the first failure's status; a child that fails stops the rest,
  // which could otherwise wait forever at a barrier.  If a fork fails, the
  // children already started are killed and reaped before the error is
  // thrown, and every child dies with the parent (PR_SET_PDEATHSIG).
  static int Run(std::vector<int> cpus, const std::function<int(ParallelInstances&)>& body) {
    if (cpus.empty()) cpus.push_back(-1);
    void* mem = ::mmap(nullptr, sizeof(Shared), PROT_READ | PROT_WRITE,
                       MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (mem == MAP_FAILED) throw std::runtime_error("mmap of the instance barrier failed");
    Shared* shared = new (mem) Shared{};
    std::fflush(nullptr);  // children must not repeat buffered output
    const pid_t parent = ::getpid();
    std::vector<pid_t> pids;
    for (unsigned i = 0; i < cpus.size(); ++i) {
      const pid_t pid = ::fork();
      if (pid < 0) {
        const int error = errno;
        for (const pid_t started : pids) ::kill(started, SIGKILL);
        for (const pid_t started : pids) {
          while (::waitpid(started, nullptr, 0) < 0 && errno == EINTR) {}
        }
        ::munmap(mem, sizeof(Shared));
        throw std::runtime_error(std::string("fork failed: ") + std::strerror(error));
      }
      if (pid == 0) {
        // A parent that dies (a signal, an uncaught exception) takes its
        // instances with it rather than leaving them at a barrier.
        if (::prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 || ::getppid() != parent) ::_exit(2);
        int status = 1;
        try {
          if (cpus[i] >= 0) {
            cpu_set_t set;
            CPU_ZERO(&set);
            CPU_SET(cpus[i], &set);
            if (sched_setaffinity(0, sizeof(set), &set) != 0) {
              throw std::runtime_error("sched_setaffinity failed");
            }
          }
          ParallelInstances self(shared, i, unsigned(cpus.size()), cpus[i]);
          status = body(self);
        } catch (const std::exception& e) {
          std::fprintf(stderr, "instance %u: error: %s\n", i, e.what());
          status = 2;
        }
        std::fflush(nullptr);
        ::_exit(status);
      }
      pids.push_back(pid);
    }
    int result = 0;
    // Waits for this call's children only, and signals only those not yet
    // reaped (a reaped child's pid may already belong to another process).
    while (!pids.empty()) {
      int wstatus = 0;
      const pid_t pid = ::waitpid(-1, &wstatus, 0);
      if (pid < 0) {
        if (errno == EINTR) continue;
        break;
      }
      const auto at = std::find(pids.begin(), pids.end(), pid);
      if (at == pids.end()) continue;  // not an instance
      pids.erase(at);
      const int code = WIFEXITED(wstatus) ? WEXITSTATUS(wstatus) : 128 + WTERMSIG(wstatus);
      if (code != 0 && result == 0) {
        result = code;
        for (const pid_t other : pids) ::kill(other, SIGKILL);
      }
    }
    ::munmap(mem, sizeof(Shared));
    return result;
  }

  unsigned index() const { return index_; }
  unsigned count() const { return count_; }
  int cpu() const { return cpu_; }

  // Waits until every instance arrives; all of them return instance 0's
  // `proceed`, so a decision taken on one clock (another repetition?) keeps
  // the barrier counts equal.
  bool Sync(bool proceed = true) {
    const uint32_t gen = s_->generation.load(std::memory_order_acquire);
    // Instance 0 posts this round's verdict before arriving.  Rounds
    // alternate slots, so a slow reader of the previous round's verdict is
    // never overwritten: the next round cannot finish without it.
    if (index_ == 0) s_->verdict[gen & 1].store(proceed ? 1 : 0, std::memory_order_relaxed);
    if (s_->arrived.fetch_add(1, std::memory_order_acq_rel) + 1 == count_) {
      s_->arrived.store(0, std::memory_order_relaxed);
      s_->generation.store(gen + 1, std::memory_order_release);
    } else {
      while (s_->generation.load(std::memory_order_acquire) == gen) __builtin_ia32_pause();
    }
    return s_->verdict[gen & 1].load(std::memory_order_relaxed) != 0;
  }

  // Runs `print` on each instance in turn, so their output lines never
  // interleave.
  template <class F>
  void InTurn(F print) {
    for (unsigned i = 0; i < count_; ++i) {
      Sync();
      if (i == index_) {
        print();
        std::fflush(stdout);
      }
    }
    Sync();
  }

 private:
  struct Shared {
    alignas(64) std::atomic<uint32_t> arrived{0};
    alignas(64) std::atomic<uint32_t> generation{0};
    std::atomic<uint32_t> verdict[2] = {};
  };

  ParallelInstances(Shared* s, unsigned index, unsigned count, int cpu)
      : s_(s), index_(index), count_(count), cpu_(cpu) {}

  Shared* s_;
  unsigned index_, count_;
  int cpu_;
};

}  // namespace benchmark_support
