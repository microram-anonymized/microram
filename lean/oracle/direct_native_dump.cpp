// Original-input fixtures from the real level-one LevelMergeJob. Kept outside
// CMake's tests glob. Full payload bytes are little-endian Nat identities;
// only kMetaResidualClass is scratch. No reference/model answer is generated.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>
#include "src/crypto/hash_primitives.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"
namespace bs = microram::byteslice;
namespace la = bs::levelarena;
namespace ts = bs::test_support;
using RK = microram::crypto::AesRoundKeys;
struct Config {
  unsigned digit=1, flushes=2; size_t stash=1, tier=1;
  size_t fresh=96, older=0, old_tier=0;
  int target=-1; unsigned spread=1; bool versions=false; uint64_t seed=0x5EED0C0DEull;
};
uint64_t Word(const RK& rk, bs::RebuildNonce n, bs::KeyWords k) {
  return microram::crypto::AesCtrTagU128WordsHost(n.real_lo,n.real_hi,k.w0,k.w1,rk);
}
size_t Home(uint64_t w, size_t U, unsigned d) {
  unsigned power=static_cast<unsigned>(__builtin_ctz(d));
  size_t block=U<<power; unsigned radix=d>>power;
  return (w&(block-1)) + block*((w>>bs::Log2Exact(block))%radix);
}
std::string Rec(const bs::Layout& l,const uint8_t* p,size_t lane) {
  auto k=ts::SlotKeyWordsOf(l,p,lane); if(k.w1) throw std::logic_error("wide key unsupported");
  uint64_t v=0; uint8_t meta=0;
  for(size_t i=0;i<l.value_bytes;++i) {
    uint8_t b=p[(l.key_bytes+i)*64+lane];
    if(i+1==l.value_bytes) {b&=~bs::kMetaResidualClass;meta=b;}
    v|=uint64_t{b}<<(8*i);
  }
  return "{\"key\":"+std::to_string(k.w0)+",\"value\":"+std::to_string(v)+
    ",\"tombstone\":"+((meta&bs::kMetaErased)?"true":"false")+"}";
}
std::string Lanes(const bs::TableView& t) {
  std::string s="[";
  for(size_t b=0;b<t.num_buckets;++b) {if(b)s+=",";s+="[";
    for(size_t i=0;i<64;++i){if(i)s+=",";s+=((t.masks[b]>>i)&1)?Rec(t.layout,t.Bucket(b),i):"null";}
    s+="]";
  } return s+"]";
}
std::string Tier(const bs::Layout& l,const bs::ResidualStash& t,bool padded=false) {
  std::string s="[";bool first=true;
  for(size_t b=0;b<t.num_buckets;++b)for(size_t i=0;i<64;++i) {
    bool live=(t.masks[b]>>i)&1;if(!live&&!padded)continue;
    if(!first)s+=",";first=false;s+=live?Rec(l,t.Bucket(b),i):"null";
  }return s+"]";
}
std::string Escape(std::string s) {std::string t="\"";for(char c:s){if(c=='\"'||c=='\\')t+='\\';t+=c;}return t+"\"";}
void Run(const Config& c,const char* path) {
  bs::Layout l;l.key_bytes=8;l.value_bytes=8;l.tag_bytes=4;
  auto rk=microram::crypto::DeriveAesRoundKeys(microram::crypto::SecretKeySeed::Fixed(c.seed));
  auto keys=bs::MakeAesTagKeys(rk);
  la::LevelArenaGeometry::Params p;p.branching=8;p.levels=3;p.top_digit=2;
  p.prefix_flushes=c.flushes;p.stash_buckets=c.stash;p.tier_buckets=c.tier;
  la::LevelArenaGeometry g(p);la::LevelArenaStashSizing sizing(g,uint64_t{1}<<32);
  auto nonce=la::FamilyNonce(la::CanonicalFamily(g,1,c.digit));
  auto old=la::FamilyNonce(la::CanonicalFamily(g,1,c.digit>1?c.digit-1:1));
  size_t U=g.CarryBuckets(1);
  if(c.target>=0&&size_t(c.target)+c.spread>c.digit*U)throw std::invalid_argument("target homes outside output");
  if(c.older>(c.digit-1)*U*64)throw std::invalid_argument("too many old records");
  unsigned radix=c.digit>>__builtin_ctz(c.digit);
  auto shape=la::MakeMergeShape(U,c.digit,radix);
  auto pool=la::FinishPoolShapeAt(g,sizing.Buckets(1),1,shape);
  auto range=la::LevelFinishRangePlan(pool);
  bool dfs=c.digit>1&&bs::DfsResidualRangeApplies(pool.swept_buckets-pool.direct_buckets,pool.main_levels);
  size_t output_width=c.tier*64,route_width=sizing.Buckets(1)*64;
  size_t insertion_width=la::MergeStashBuckets(g,sizing.Buckets(1),1)*64;
  auto out=ts::ZeroedTable(c.digit*U,l);
  auto a=ts::ZeroedTable(std::max(size_t{1},(c.digit-1)*U),l);
  auto prefix=ts::ZeroedTable(g.DensePrefixBuckets(),l);
  auto tier_store=ts::ZeroedTable(c.tier,l);bs::ResidualStash tier;
  tier.data=tier_store.data.get();tier.num_buckets=c.tier;tier.entry_bytes=l.EntryBytes();
  auto old_store=ts::ZeroedTable(c.tier,l);bs::ResidualStash atier;
  atier.data=old_store.data.get();atier.num_buckets=c.tier;atier.entry_bytes=l.EntryBytes();
  std::map<uint64_t,uint64_t> words,old_words;uint64_t next=1;
  std::vector<bs::KeyWords> akeys,fkeys;
  auto candidate=[&](int target,unsigned d){for(;;){auto k=ts::FixtureKey(next++,8);
    uint64_t w=Word(rk,nonce,k);if(target<0||Home(w,U,d)==size_t(target)){words[k.w0]=w;return k;}}};
  for(size_t i=0;i<c.older;++i){bs::KeyWords k;uint64_t w;size_t home;auto b=bs::View(a);unsigned lane;
    size_t attempts=0;do {if(++attempts>1000000)throw std::invalid_argument("cannot fill valid old placement with target");
      k=candidate(c.target<0?-1:c.target+int(i%c.spread),c.digit);w=Word(rk,old,k);home=Home(w,U,c.digit-1);lane=__builtin_popcountll(b.masks[home]);}while(lane==64);
    ts::PlantEntry(l,b.Bucket(home),lane,k,1,(i%11==0)?bs::kMetaErased:0);b.masks[home]|=uint64_t{1}<<lane;
    old_words[k.w0]=w;akeys.push_back(k);
  }
  for(size_t i=0;i<c.old_tier;++i){auto k=candidate(c.target,c.digit);size_t b=i/64,lane=i%64;
    ts::PlantEntry(l,atier.Bucket(b),lane,k,1);atier.masks[b]|=uint64_t{1}<<lane;old_words[k.w0]=Word(rk,old,k);akeys.push_back(k);}
  if(c.fresh>g.DensePrefixBuckets()*64)throw std::invalid_argument("too many prefix records");
  for(size_t i=0;i<c.fresh;++i){size_t unit=i/(c.stash*64);bs::KeyWords k;
    if(c.versions&&unit>0&&i%(c.stash*64)<fkeys.size()) k=fkeys[i%(c.stash*64)];
    else if(c.versions&&!akeys.empty()&&i<akeys.size()) k=akeys[i];
    else k=candidate(c.target<0?-1:c.target+int(i%c.spread),c.digit);
    if(unit==0)fkeys.push_back(k);
    size_t b=i/64,lane=i%64;ts::PlantEntry(l,prefix.Bucket(b),lane,k,static_cast<uint8_t>(2+unit),
      c.versions&&((i+unit)%3==0)?bs::kMetaErased:0);prefix.masks[b]|=uint64_t{1}<<lane;
  }
  std::string original_a=c.digit==1?"[]":Lanes(bs::View(a)),original_tier=Tier(l,atier);
  std::string units="[";auto pv=bs::View(prefix);
  for(size_t u=0;u<c.flushes;++u){if(u)units+=",";std::string lanes="[";
    for(size_t b=0;b<c.stash;++b)for(size_t lane=0;lane<64;++lane){if(b||lane)lanes+=",";
      size_t pos=u*c.stash+b;lanes+=((pv.masks[pos]>>lane)&1)?Rec(l,pv.Bucket(pos),lane):"null";}
    units+=lanes+"]";}units+="]";
  uint64_t prefix_digest=ts::DigestTable(bs::View(prefix)),a_digest=ts::DigestTable(bs::View(a));
  uint64_t atier_digest=ts::DigestStash(l,atier);
  la::LevelMergeBinding binding;binding.ordinal=c.digit;binding.out=bs::View(out);
  binding.out_tier=&tier;binding.destination_generation=1;
  if(c.digit>1){binding.older_main=bs::View(a);binding.older_tier=&atier;}
  la::LevelCarry incoming;incoming.ordinal=c.digit;incoming.dense_prefix=bs::View(prefix);
  la::LevelMergeJob job(g,sizing,l,1,*keys);
  la::LevelMergeScratch scratch(l,la::MaxLevelMergeRangeBuckets(g,sizing,1),la::MaxLevelDfsAllocation(g,sizing,1));
  bs::SubtaskBudget budget{~size_t{0},~size_t{0},~size_t{0},~size_t{0},~size_t{0},~size_t{0}};
  std::string observations="{",message,phase="prepareA",site;bool first=true;
  auto observation=[&](std::string name,std::string value){if(!first)observations+=",";first=false;observations+=Escape(name)+":"+value;};
  bool success=false;job.Begin(binding);
  try {
    job.PrepareOlder(budget);
    if(c.digit>1) {
      observation("a_main",Lanes(binding.out));std::string stashes="[";
      for(unsigned i=0;i<shape.block_bits;++i){if(i)stashes+=",";stashes+=Tier(l,job.older_sheds()[i]);}stashes+="]";
      observation("a_stashes",stashes);
      observation("a_radix",shape.has_radix_pass()?Tier(l,job.older_sheds()[shape.block_bits+la::kLevelMergeRadixStashOffset]):"[]");
    }
    phase="produceB";job.InstallCarry(incoming,budget);
    observation("b_tier",Tier(l,c.digit>1?*job.dense_tier():tier));
    phase="finish";job.FinishMerge(&scratch,budget);success=true;
  }catch(const std::runtime_error& e){message=e.what();
    if(message.find(" phase ran out of room at ")==std::string::npos)throw;
    if(message.find("dense-drain")!=std::string::npos)site=c.digit>1?"bTier":"outputTier";
    else if(message.find("dfs")!=std::string::npos){phase="distributeA";site="dfs";}
    else if(message.find("radix")!=std::string::npos)site="radix";
    else if(phase=="prepareA"&&(message.find("butterfly")!=std::string::npos||message.find("cross-level")!=std::string::npos||message.find("route-level")!=std::string::npos))site="route";
    else if(message.find("drain")!=std::string::npos){phase="drain";site="outputTier";}
    else if(message.find("merge")!=std::string::npos)site="insertion";
    else throw;
    job.Cancel();
  }
  observations+="}";
  if(prefix_digest!=ts::DigestTable(bs::View(prefix))||a_digest!=ts::DigestTable(bs::View(a))||
    atier_digest!=ts::DigestStash(l,atier))throw std::logic_error("source changed");
  std::string ranges=dfs?"{\"kind\":\"dfs\",\"index_bits\":"+std::to_string(range.index_bits)+
    ",\"range_bits\":"+std::to_string(range.range_bits)+",\"pool_capacity\":"+std::to_string((pool.swept_buckets-pool.direct_buckets)*64)+"}":"{\"kind\":\"direct\"}";
  std::string expected=success?"{\"kind\":\"published\",\"main\":"+Lanes(binding.out)+",\"tier\":"+Tier(l,tier,true)+"}":
    "{\"kind\":\"failed\",\"phase\":"+Escape(phase)+",\"site\":{\"kind\":"+Escape(site)+"}}";
  std::ofstream f(path);if(!f)throw std::runtime_error("cannot open output");
  f<<"{\"format\":\"direct-job-native/0\",\"evidence\":\"native-differential\",\"geometry\":{\"K\":"<<bs::Log2Exact(U)
   <<",\"digit\":"<<c.digit<<",\"output_homes\":"<<c.digit*U<<",\"output_capacity\":"<<output_width
   <<",\"a_tier_capacity\":"<<(c.digit>1?c.tier*64:0)<<",\"route_capacity\":"<<route_width<<",\"radix_capacity\":"<<route_width
   <<",\"insertion_capacity\":"<<insertion_width<<",\"copy_capacity\":"<<output_width<<",\"ranges\":"<<ranges<<"},\"inputs\":{\"a_main\":"
   <<original_a<<",\"a_tier\":"<<original_tier<<",\"units\":"<<units<<"},\"words\":[";
  first=true;for(auto kv:words){if(!first)f<<",";first=false;f<<"{\"family\":\"current\",\"key\":"<<kv.first<<",\"word\":"<<kv.second<<"}";}
  for(auto kv:old_words)f<<",{\"family\":\"old\",\"key\":"<<kv.first<<",\"word\":"<<kv.second<<"}";
  f<<"],\"observations\":"<<observations<<",\"expected\":"<<expected<<",\"native\":{\"message\":"<<Escape(message)
   <<",\"key_bytes\":8,\"value_bytes\":8,\"prefix_flushes\":"<<c.flushes<<",\"stash_buckets\":"<<c.stash
   <<",\"source_unchanged\":true,\"published\":"<<(success?"true":"false")<<"}}\n";
  if(!f)throw std::runtime_error("fixture write failed");
}
int main(int argc,char**argv){try{if(argc<2)throw std::invalid_argument("usage: direct_native_dump OUT [--digit N --flushes N --stash N --tier N --fresh N --older N --old-tier N --target N --spread N --versions N --seed N]");
  Config c;for(int i=2;i<argc;i+=2){if(i+1==argc)throw std::invalid_argument("missing value");std::string a=argv[i];size_t parsed=0;auto v=std::stoull(argv[i+1],&parsed,0);
    if(parsed!=std::strlen(argv[i+1])||(a!="--seed"&&v>1000000))throw std::invalid_argument("invalid option value");
    if(a=="--digit")c.digit=v;else if(a=="--flushes")c.flushes=v;else if(a=="--stash")c.stash=v;else if(a=="--tier")c.tier=v;
    else if(a=="--fresh")c.fresh=v;else if(a=="--older")c.older=v;else if(a=="--old-tier")c.old_tier=v;else if(a=="--target")c.target=v;
    else if(a=="--spread")c.spread=v;else if(a=="--versions")c.versions=v;else if(a=="--seed")c.seed=v;else throw std::invalid_argument("unknown option");}
  if(c.digit<1||c.digit>8||(c.digit==1&&(c.older||c.old_tier))||c.old_tier>c.tier*64||c.spread==0||c.tier<1||c.tier>8)throw std::invalid_argument("invalid harness input");
  Run(c,argv[1]);return 0;}catch(const std::exception&e){std::fprintf(stderr,"direct_native_dump: %s\n",e.what());return 2;}}
