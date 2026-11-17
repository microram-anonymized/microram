// Cross-check of the initialization path through the REAL public engine:
// LevelArenaEngine::Initialize (its own scatter, thread-free inline executor,
// LevelState::PublishInitialTop, RouteInitialTop), then the published top is
// read back lane by lane from the publisher's live table.  Writes a
// "top-init-fixture/0" with "engine_path":true (no scattered-main field: the
// scatter is internal to the engine) so the same model_tp.py compares it.
//
//   fdtp_engine OUT.json --B 2 --L 2 --D 2 --r0 2 --s 1 --count N
//                [--in-force h:n,...] [--no-shuffle] [--key-seed HEX] [--seed S]
#define FDTP_NO_MAIN
#include "fdtp.cpp"

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"

int main(int argc, char** argv) {
  Config cfg;
  cfg.mode = "init";
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    const auto arg = [&]() -> const char* { return argv[++i]; };
    const auto num = [&]() { return std::strtoull(arg(), nullptr, 10); };
    if (a == "--B") cfg.B = num();
    else if (a == "--L") cfg.L = num();
    else if (a == "--D") cfg.D = num();
    else if (a == "--r0") cfg.r0 = num();
    else if (a == "--s") cfg.s = num();
    else if (a == "--count") cfg.count = num();
    else if (a == "--in-force") cfg.in_force = arg();
    else if (a == "--no-shuffle") cfg.in_shuffle = 0;
    else if (a == "--key-seed") cfg.key_seed = std::strtoull(arg(), nullptr, 16);
    else if (a == "--seed") cfg.seed = num();
    else if (a[0] != '-') cfg.out_path = argv[i];
    else { std::fprintf(stderr, "unknown %s\n", a.c_str()); return 2; }
  }
  try {
    la::LevelArenaEngine::Options o;
    o.geometry.branching = cfg.B;
    o.geometry.levels = cfg.L;
    o.geometry.top_digit = cfg.D;
    o.geometry.prefix_flushes = cfg.r0;
    o.geometry.stash_buckets = cfg.s;
    o.geometry.dense_prefixes = 2;
    o.key_bytes = 8;
    o.value_bytes = 7;
    o.max_accesses = uint64_t{1} << 32;
    o.flush_policy = la::LevelArenaEngine::FlushPolicy::kSettle;
    o.secret_seed = microram::crypto::SecretKeySeed::Fixed(cfg.key_seed);
    const la::LevelArenaGeometry resolved(
        la::ResolveLevelArenaTierGeometry(o.geometry, o.max_accesses));
    cfg.tb = resolved.TierBucketsOf(resolved.TopLevel());
    cfg.acc = 32;
    World w;
    const auto routing_keys =
        microram::crypto::DeriveRoutingAesRoundKeys(*o.secret_seed);
    BuildWorld(cfg, &w, /*ordinal=*/cfg.D, &routing_keys);
    const size_t T = w.T;
    std::mt19937_64 rng(cfg.seed * 0x9E3779B97F4A7C15ull + 777);
    std::vector<bs::KeyWords> input;
    for (auto& f : ParseForce(cfg.in_force))
      for (long n = 0; n < f.second && input.size() < cfg.count; ++n)
        input.push_back(w.pool.Take(f.first));
    while (input.size() < cfg.count) input.push_back(w.pool.Take(rng() % T));
    if (cfg.in_shuffle) std::shuffle(input.begin(), input.end(), rng);
    std::vector<std::array<uint8_t, 8>> keys(input.size()), values(input.size());
    for (size_t i = 0; i < input.size(); ++i) {
      std::memcpy(keys[i].data(), &input[i].w0, 8);
      for (size_t b = 0; b < 8; ++b) values[i][b] = static_cast<uint8_t>(rng());
    }
    la::LevelArenaEngine engine(o);
    bool failed = false;
    std::string message;
    try {
      InputIt it{&keys, &values, 0};
      engine.Initialize(it, cfg.count);
    } catch (const std::runtime_error& e) {
      failed = true;
      message = e.what();
    }
    const bs::Layout layout = la::LevelArenaStoredLayout(8, 7, resolved);
    std::vector<Rec> out_main, out_tier;
    size_t tier_pages = 0;
    if (!failed) {
      bool found = false;
      for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
        if (t.owner != w.top || t.main_buckets != T) continue;
        found = true;
        bs::TableView mv;
        mv.layout = layout;
        mv.num_buckets = t.main_buckets;
        mv.data = t.data;
        mv.masks = t.masks;
        out_main = Collect(layout, mv);
        bs::ResidualStash tv;
        tv.entry_bytes = layout.EntryBytes();
        tv.num_buckets = t.tier_buckets;
        tv.data = t.tier_data;
        for (size_t b = 0; b < t.tier_buckets; ++b) tv.masks[b] = t.tier_masks[b];
        tier_pages = t.tier_buckets;
        out_tier = Collect(layout, tv);
      }
      if (!found) throw std::runtime_error("the published top was not found");
    }
    std::set<bs::KeyWords> allkeys(input.begin(), input.end());
    std::string j;
    j += "{\"format\":\"top-init-fixture/0\",\"engine_path\":true,\n";
    j += " \"job\":{\"kind\":\"top_init_engine\",\"count\":" + std::to_string(cfg.count) + "},\n";
    bs::SubtaskBudget budget = la::WholeLevelMergeBudget();
    (void)budget;
    GeometryJson(&j, cfg, w, 0, w.geometry->OlderTierBuckets(w.top, w.geometry->TopDigit()),
                 tier_pages ? tier_pages : cfg.tb, 64 * (tier_pages ? tier_pages : cfg.tb), nullptr);
    j += " \"input\":[";
    for (size_t i = 0; i < input.size(); ++i) {
      j += i == 0 ? "\n  " : ",\n  ";
      j += "{\"key\":\"" + Hex64(input[i].w0) + "\",\"value\":\"" + HexBytes(values[i].data(), 7) + "\"}";
    }
    j += "],\n";
    WordsJson(&j, w, allkeys);
    j += " \"outputs\":{\"verdict\":\"";
    j += failed ? "failure" : "success";
    j += "\",\"phase\":\"" + Escape(PhaseOf(message)) + "\",\"kind\":\"" + Escape(KindOf(message)) +
         "\",\"message\":\"" + Escape(message) + "\",\n";
    RecList(&j, "main", out_main, "bucket", false);
    RecList(&j, "tier", out_tier, "page", true);
    j += " }}\n";
    char line[200];
    std::snprintf(line, sizeof(line), "count=%zu tier_pages=%zu -> %s %s", cfg.count, tier_pages,
                  failed ? "failure" : "success", failed ? KindOf(message).c_str() : "");
    WriteOut(cfg, j, line);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "fdtp_engine: harness error: %s\n", e.what());
    return 2;
  }
  return 0;
}
