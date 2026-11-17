// Public ByteMap operations, native observations only. Reuse the publication
// recorder so transient tables and prefixes cannot disappear between calls.
#define MICRORAM_BYTESLICE_BATCH_PROFILE 1
#define main hierarchy_legacy_main
#include "hierarchy_dump.cpp"
#undef main
#include "cpu_byteslice_oram/byte_map.hpp"

namespace {
struct ApiDriver {
  Opts o;
  unsigned rounds = 40, width = 5, key_bytes = 0;
  std::vector<std::string> calls;
  std::vector<std::pair<uint64_t, size_t>> groups;
  bool batch = false, cycles = false, full_init = false;
  uint32_t Mask(uint32_t v) const { return o.V == 1 ? v & 255u : v; }
  uint64_t seed_positions = 0;
  static std::string Bool(bool b) { return b ? "true" : "false"; }
  void OpRecord(Run& r, uint64_t key, int kind = kRead, uint32_t value = 0, bool insert = false) {
    Op op; op.key = key; op.kind = kind; op.insert = insert;
    if (kind == kWrite || kind == kWriteNp || kind == kExchange) {
      op.value.resize(o.V); std::memcpy(op.value.data(), &value, o.V);
    }
    r.ops_.push_back(op);
    r.all_keys_.insert(key);
  }
  void Finish(Run& r, std::string j) {
    r.access_ = r.ops_.size();
    if (r.eng_->dense().positions() - seed_positions != r.access_)
      throw HarnessError("public API primitive count differs from native dense cursor");
    r.CaptureNewPrefixes();
    if (cycles && !r.StepLoop()) throw HarnessError("API cycle capacity failure");
    r.Snapshot("api-call");
    const auto& d = r.eng_->dense();
    std::string current, partial;
    LanesJson(&current, ReadStore(r.layout_, {d.BucketAt(d.UnitBase()), d.MaskAt(d.UnitBase()),
      d.unit_buckets(), r.layout_.BucketBytes()}), true);
    const size_t prefix_base = d.RingSlot(d.complete_prefixes()) * d.prefix_buckets();
    LanesJson(&partial, ReadStore(r.layout_, {d.BucketAt(prefix_base), d.MaskAt(prefix_base),
      d.units_in_prefix_ * d.unit_buckets(), r.layout_.BucketBytes()}), true);
    j += ",\"top_ordinal\":" + Dec(r.eng_->level(r.Lv()).ordinal());
    j += ",\"position\":" + Dec(r.access_) + ",\"current\":" + current + ",\"partial\":" + partial + ",\"groups\":[";
    for (size_t i = 0; i < groups.size(); ++i)
      j += (i ? "," : "") + std::string("[") + Dec(groups[i].first) + "," + Dec(groups[i].second) + "]";
    calls.push_back(j + "]}");
    groups.clear();
  }
  int RunAll() {
    o.V = cycles ? 4 : 1; o.K = key_bytes ? key_bytes : cycles ? 4 : 8;
    key_codec.Configure(o.K,o.secret);
    o.sequential_keys = cycles;
    o.batch_lanes = width; o.lazy = !cycles; o.policy_auto = !cycles;
    Run r(o);
    r.eng_owner_ = std::make_unique<la::LevelArenaEngine>(MakeOptions(o, false));
    r.eng_ = r.eng_owner_.get();
    r.g_ = &r.eng_->geometry(); r.sz_ = &r.eng_->sizing(); r.layout_ = r.eng_->layout();
    o.keys = cycles ? r.g_->CapacityEntries() : 128;
    o.init = cycles ? (full_init ? o.keys : 0) : 32; o.init_set = true;
    r.words_.rk = microram::crypto::DeriveRoutingAesRoundKeys(microram::crypto::SecretKeySeed::Fixed(o.secret));
    g_run = &r; la::SetArenaPauseHook(PauseHook);
    r.BuildTrace(); r.Snapshot("construct");
    std::vector<std::array<uint8_t,64>> init_keys(r.init_keys_.size());
    for (size_t i = 0; i < init_keys.size(); ++i) init_keys[i] = key_codec.User(r.init_keys_[i]);
    if (!init_keys.empty()) r.eng_->Initialize(InputIt{&init_keys, &r.init_values_, 0}, init_keys.size());
    r.seed_prefixes_ = r.captured_ = r.eng_->dense().complete_prefixes();
    r.hook_capture_ = true; r.Snapshot("initialize");
    seed_positions = r.eng_->dense().positions();
    cpu_byteslice_oram::ByteMap<> map(r.g_->CapacityEntries(), o.K, o.V, std::move(r.eng_owner_));
    r.extra_reader_ = [&] {
      groups.push_back({r.eng_->dense().positions() - seed_positions,
                       batch ? r.eng_->tiles_[0]->lanes : 1});
    };
    for (unsigned round = 0; round < rounds; ++round) {
      const uint64_t key = 1 + round % 23;
      uint32_t value = Mask(round % 5 == 0 ? 0 : round * (cycles ? 0x1020304u : 7u));
      map.write(key_codec.User(key).data(), reinterpret_cast<const uint8_t*>(&value));
      OpRecord(r,key,kWriteNp,value);
      Finish(r,"{\"kind\":\"write\",\"key\":"+Dec(key)+",\"value\":"+Dec(value));
      // Each mode covers a hit, an absent key, destination collision, same-key
      // rename, and exceptions after modifying the temporary buffers.
      for (unsigned mode = 0; mode < 6; ++mode) {
        const bool mut = mode % 2, throwing = mode >= 4;
        uint64_t source = mode == 2 || mode == 3 ? (cycles ? 100 + (round * 7 + mode) % 2000 : 10000 + round * 7 + mode) : key;
        uint64_t destination = round % 3 == 0 ? source : (round % 3 == 1 ? key : 50 + round % 17);
        key_codec.User(destination);
        uint32_t delta = cycles ? 0x1020304u + round * 0x10001u : 3 + round % 19, before = 0, after = 0;
        bool present = false, returned = false, caught = false; unsigned invocations = 0;
        auto body = [&](uint8_t* bytes, bool found) {
          ++invocations; std::memcpy(&before,bytes,o.V); present = found;
          after = Mask(before + delta + (found ? 17 : 31));
          std::memcpy(bytes,&after,o.V);
        };
        try {
          if (mut) returned = map.Access(key_codec.User(source).data(),
            [&](uint8_t* k, uint8_t* v, bool f) {
              body(v,f); std::memcpy(k,key_codec.User(destination).data(),o.K);
              if (throwing) throw std::runtime_error("api fixture callback");
            });
          else returned = map.Access(key_codec.User(source).data(),
            [&](uint8_t* v, bool f) { body(v,f); if (throwing) throw std::runtime_error("api fixture callback"); });
        } catch (const std::runtime_error& ex) {
          if (std::string(ex.what()) != "api fixture callback") throw;
          caught = true;
        }
        OpRecord(r,source,throwing ? kRead : mut ? kErase : kWrite,after);
        if (mut && !caught) OpRecord(r,destination,kWriteNp,after);
        Finish(r,"{\"kind\":\"callback\",\"key\":"+Dec(source)+",\"mutable_key\":"+Bool(mut)+
          ",\"destination\":"+Dec(destination)+",\"delta\":"+Dec(delta)+",\"throws\":"+Bool(throwing)+
          ",\"input\":"+Dec(before)+",\"found\":"+Bool(present)+",\"invocations\":"+Dec(invocations)+
          ",\"exception\":"+Bool(caught)+",\"returned\":"+(caught ? "null" : Bool(returned)));
      }
      // Includes empty/width boundaries, duplicates, blind separators, explicit
      // ReadThenWrite, both exchange policies, and presence-forced probing.
      const size_t sizes[] = {0,1,width-1,width,width+1,2*width+3,67};
      const size_t n = sizes[round % 7]; const bool found_output = round % 2;
      std::vector<uint64_t> keys(n); std::vector<uint32_t> inputs(n), outputs(n,0xD3); std::vector<uint8_t> found(n,0xA7);
      std::vector<bs::BatchRequest> req(n); std::string lanes="[";
      const bs::BatchOp kinds[] = {bs::BatchOp::kWrite,bs::BatchOp::kRead,bs::BatchOp::kWrite,
        bs::BatchOp::kReadThenWrite,bs::BatchOp::kErase,bs::BatchOp::kExchange};
      const char* names[] = {"write","read","write","readThenWrite","erase","exchange"};
      for (size_t i = 0; i < n; ++i) {
        const size_t kind = i % 6; const bool out = kind != 0 && (i + round) % 4 != 0;
        keys[i] = 1 + (i / 3 + round) % 29; inputs[i] = Mask(round * (cycles ? 0x1020304u : 11u) + i);
        req[i] = {kinds[kind], (i + round) % 2 != 0, key_codec.User(keys[i]).data(),
          reinterpret_cast<const uint8_t*>(&inputs[i]), out ? reinterpret_cast<uint8_t*>(&outputs[i]) : nullptr};
        lanes += (i ? "," : "") + std::string("{\"key\":")+Dec(keys[i])+",\"value\":"+Dec(inputs[i])+
          ",\"kind\":\""+names[kind]+"\",\"value_output\":"+Bool(out)+",\"insert\":"+Bool(req[i].insert)+"}";
      }
      batch = true;
      map.access_batch(n,req.data(),found_output ? found.data() : nullptr);
      batch = false;
      std::string responses="[";
      for (size_t i = 0; i < n; ++i) {
        const auto op = req[i].op;
        const int primitive = op == bs::BatchOp::kRead ? kRead : op == bs::BatchOp::kErase ? kErase
          : op == bs::BatchOp::kExchange ? kExchange
          : op == bs::BatchOp::kWrite && !req[i].value_out && !found_output ? kWriteNp : kWrite;
        OpRecord(r,keys[i],primitive,inputs[i],req[i].insert);
        responses += (i ? "," : "") + std::string("{\"value\":")+
          (req[i].value_out ? Dec(outputs[i]) : "null")+",\"found\":"+(found_output ? Bool(found[i]) : "null")+"}";
      }
      Finish(r,"{\"kind\":\"batch\",\"found_output\":"+Bool(found_output)+",\"lanes\":"+lanes+
        "],\"responses\":"+responses+"]");
    }
    r.extra_reader_ = {}; if (!r.StepLoop()) throw HarnessError("API run capacity failure");
    if (!r.hook_error_.empty()) throw HarnessError(r.hook_error_);
    o.accesses = r.access_; // requested primitive count, checked by both readers
    r.extra_json_ = "\"api\":{\"format\":\"public-api/0\",\"settle_after_call\":"+Bool(cycles)+",\"width\":"+Dec(width)+",\"calls\":[";
    for (size_t i=0;i<calls.size();++i) r.extra_json_ += (i ? "," : "") + calls[i];
    r.extra_json_ += "]}";
    r.Write(); la::SetArenaPauseHook(nullptr); g_run = nullptr;
    for (const auto& c:r.checks_) std::fprintf(stderr,"API check: %s\n",c.c_str());
    std::printf("API: %zu calls, %zu primitives, %zu publications\n",calls.size(),r.access_,r.tables_.size());
    return r.checks_.empty() ? 0 : 1;
  }
};
}
int main(int argc,char** argv) {
  try {
    ApiDriver d; d.o.B=8;d.o.L=4;d.o.D=8;d.o.r0=2;d.o.fanouts={4,4,4};
    for(int i=1;i<argc;++i) {
      const std::string a=argv[i];
      if(a=="--geometry31") {d.o.selected="geometry31";d.o.B=8;d.o.L=8;d.o.D=8;d.o.r0=8;
        d.o.fanouts={4,4,8,8,8,8,8};d.o.skip_top=true;}
      else if(a=="--cycles") {d.cycles=true; d.o.B=4; d.o.L=3; d.o.D=4; d.o.r0=2; d.o.fanouts={4,2};}
      else if(a=="--full-init") d.full_init=true;
      else if(a=="--K" && i+1<argc) d.key_bytes=std::stoul(argv[++i]);
      else if(a=="--rounds" && i+1<argc) d.rounds=std::stoul(argv[++i]);
      else if(a=="--width" && i+1<argc) d.width=std::stoul(argv[++i]);
      else if(a=="--secret" && i+1<argc) d.o.secret=std::stoull(argv[++i],nullptr,16);
      else if(a[0]!='-' && !d.o.out) d.o.out=argv[i];
      else throw HarnessError("usage: api_native_dump OUT [--geometry31 | --cycles [--full-init]] [--K BYTES --rounds N --width N --secret HEX]");
    }
    if(d.key_bytes && d.key_bytes != 4 && d.key_bytes != 8 && (d.key_bytes < 9 || d.key_bytes > 64)) throw HarnessError("--K must be 4, 8, or 9..64");
    if(d.cycles && !d.o.selected.empty()) throw HarnessError("--cycles and --geometry31 are exclusive");
    if(d.full_init && !d.cycles) throw HarnessError("--full-init requires --cycles");
    if(!d.o.out || !d.rounds || !d.width || d.width>64) throw HarnessError("invalid API fixture options");
    return d.RunAll();
  }catch(const std::exception& e){std::fprintf(stderr,"api_native_dump: %s\n",e.what());return 2;}
}
