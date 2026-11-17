// Tests TieredPageMaps: append preflight and reservation, capacity admission,
// read lane admission, top-tier backend selection and minimum hierarchical
// capacity.

#include "fixture.hpp"
#include "page_map.hpp"

#include <iostream>
#include <limits>
#include <string>

namespace {

using namespace ethereum_mpt;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("page map test: ") + message);
}

template <class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const std::invalid_argument&) {
        return;
    }
    throw std::runtime_error(std::string("page map test accepted: ") + message);
}

void test_append_and_preflight() {
    const auto image = pack_generation({make_fixture()}, TierProfile{3, 0});
    const auto first = image.pages[2].size();
    const std::array<std::size_t, 3> capacities{
        image.pages[0].size(), 0, first + 20};
    TieredPageMaps maps(image, 64, capacities);
    PageStore& store = maps;
    require(store.capacities() == capacities, "explicit logical capacity limits");
    require(maps.map(Tier::bulk)->capacity() >= capacities[2], "rounded backend capacity");
    require(maps.map(Tier::storage_top) == nullptr, "disabled tier remains absent");
    require(maps.map(Tier::account_top)->backend() == PageBackend::tree &&
            maps.map(Tier::bulk)->backend() == PageBackend::tree,
            "existing constructors retain tree backends");

    std::vector<Page> pages(21);
    for (std::size_t i = 0; i < pages.size(); ++i)
        for (std::size_t j = 0; j < page_bytes; ++j)
            pages[i][j] = static_cast<std::uint8_t>(1 + i + 7 * j);

    const auto initial_accesses = maps.map(Tier::bulk)->access_count();
    reject([&] { store.write_pages_batch(Tier::bulk, first, pages); },
           "entire oversized append preflights before writing its first tile");
    reject([&] { store.write_pages_batch(Tier::bulk, 0, {pages[0]}); },
           "dummy page overwrite");
    reject([&] { store.write_pages_batch(Tier::bulk, first - 1, {pages[0]}); },
           "loaded page overwrite");
    reject([&] { store.write_pages_batch(Tier::bulk,
        std::numeric_limits<std::uint64_t>::max(), {pages[0]}); },
           "overflowing page extent");
    reject([&] { store.write_pages_batch(Tier::storage_top, 1, {pages[0]}); },
           "disabled tier append");
    reject([&] { store.write_pages_batch(static_cast<Tier>(255), 1, {pages[0]}); },
           "invalid tier append");
    require(maps.map(Tier::bulk)->access_count() == initial_accesses,
            "invalid appends perform no map accesses");

    // Seventeen pages require both a complete public tile and a one-page tail.
    pages.resize(17);
    store.write_pages_batch(Tier::bulk, first, pages);
    require(maps.map(Tier::bulk)->access_count() - initial_accesses == pages.size(),
            "one ordinary write per appended page");
    store.finish_pending_work();

    const Page last_page = pages[0];
    store.write_pages_batch(Tier::bulk, first + 19, {last_page});
    store.finish_pending_work();
    const auto after_upload = maps.map(Tier::bulk)->access_count();
    reject([&] { store.write_pages_batch(Tier::bulk, first, {last_page}); },
           "appended page overwrite");
    reject([&] { store.write_pages_batch(Tier::bulk, first + 17, {last_page}); },
           "reserved gap reuse");
    reject([&] { store.write_pages_batch(Tier::bulk, capacities[2], {last_page}); },
           "logical capacity cannot use backend rounding slack");
    store.write_pages_batch(Tier::bulk, capacities[2], {});
    require(maps.map(Tier::bulk)->access_count() == after_upload,
            "rejections and empty appends perform no writes");
    require(maps.calls() == std::array<std::uint64_t, 3>{} &&
            maps.accesses() == std::array<std::uint64_t, 3>{},
            "uploads do not alter read schedule counters");

    for (std::size_t t = 0; t < image.pages.size(); ++t) {
        if (image.pages[t].empty()) continue;
        std::vector<std::uint64_t> ids;
        for (std::size_t i = 0; i < image.pages[t].size(); ++i) ids.push_back(i);
        std::vector<Page> expected = image.pages[t];
        std::vector<std::uint8_t> presence(ids.size(), 1);
        if (t == 2) {
            for (std::size_t i = 0; i < pages.size(); ++i) {
                ids.push_back(first + i);
                expected.push_back(pages[i]);
                presence.push_back(1);
            }
            // Duplicates and dummy remain separate lanes; reserved gaps and
            // the first out-of-capacity ID stay ordinary absent-key reads.
            ids.insert(ids.end(), {first, 0, first + 17, first + 18,
                                    first + 19, capacities[2]});
            expected.insert(expected.end(), {pages[0], Page{}, Page{}, Page{},
                                             last_page, Page{}});
            presence.insert(presence.end(), {1, 1, 0, 0, 1, 0});
        }
        std::vector<Page> output(ids.size());
        std::vector<std::uint8_t> found(ids.size());
        const auto tier = static_cast<Tier>(t);
        const auto before = maps.map(tier)->access_count();
        store.read_pages_batch(tier, ids.size(), ids.data(), output.data(), found.data());
        require(output == expected && found == presence,
                "old and new pages round-trip through ordinary ORAM reads");
        require(maps.map(tier)->access_count() - before == ids.size() &&
                maps.calls()[t] == 1 && maps.accesses()[t] == ids.size(),
                "every read lane retains its schedule accounting");
    }
}

void test_capacity_admission() {
    const auto image = pack_generation({make_fixture()}, TierProfile{3, 0});
    const std::array<std::size_t, 3> counts{
        image.pages[0].size(), 0, image.pages[2].size()};
    for (const auto capacities : {
             std::array<std::size_t, 3>{0, 0, counts[2]},
             std::array<std::size_t, 3>{counts[0], 1, counts[2]},
             std::array<std::size_t, 3>{counts[0], 0, counts[2] - 1}})
        reject([&] { TieredPageMaps maps(image, 1, capacities); },
               "capacity must fit exactly the enabled tiers and initial pages");
    reject([&] { TieredPageMaps maps(image, 0, counts); }, "zero read lanes");
    reject([&] {
        TieredPageMaps maps(image, 1, counts,
            {static_cast<PageBackend>(255), PageBackend::tree});
    }, "invalid account-top backend");
    reject([&] {
        TieredPageMaps maps(image, 1, counts,
            {PageBackend::tree, static_cast<PageBackend>(255)});
    }, "invalid backend even for a disabled storage-top tier");
}

// A traversal needs max(Q, Q*K) reader lanes; a narrower reader is refused
// before the first ORAM read, and a single call wider than the reader too.
void test_read_lane_admission() {
    const auto packed = pack_snapshot(make_fixture());
    TieredPageMaps maps(packed, 2);
    require(maps.max_lanes() == 2, "reader reports its configured lanes");
    std::vector<PathRequest> requests(2);
    for (auto& request : requests) request.storage_keys.resize(2);
    reject([&] {
        BatchTraversal(packed.state_root, packed.account_root, packed.profile,
                       BatchProfile{2, 2}).run(maps, requests);
    }, "a storage phase wider than the reader's lanes");
    const std::array<std::uint64_t, 3> ids{0, 0, 0};
    std::array<Page, 3> output{};
    std::array<std::uint8_t, 3> found{};
    reject([&] {
        maps.read_pages_batch(Tier::bulk, ids.size(), ids.data(), output.data(), found.data());
    }, "a batch call wider than the reader's lanes");
    require(maps.calls() == std::array<std::uint64_t, 3>{} &&
            maps.accesses() == std::array<std::uint64_t, 3>{},
            "lane refusals perform no map reads");
    for (auto& request : requests) request.storage_keys.resize(1);
    BatchTraversal(packed.state_root, packed.account_root, packed.profile,
                   BatchProfile{2, 1}).run(maps, requests);
    require(maps.calls()[0] + maps.calls()[1] + maps.calls()[2] == 130,
            "a reader of exactly max(Q, Q*K) lanes runs both phases");
}

void test_top_backends() {
    const auto snapshot = make_fixture();
    const auto image = pack_generation({snapshot}, TierProfile{3, 3});
    const std::array<std::size_t, 3> capacities{
        image.pages[0].size() + 3, image.pages[1].size() + 3, image.pages[2].size()};
    // Test both independently selected top tiers, including a mixed layout.
    for (const auto options : {
             TieredPageMapOptions{PageBackend::hierarchical, PageBackend::hierarchical},
             TieredPageMapOptions{PageBackend::tree, PageBackend::hierarchical}}) {
        TieredPageMaps maps(image, 20, capacities, options);
        require(maps.capacities() == capacities, "top backends preserve logical limits");
        require(maps.map(Tier::bulk)->backend() == PageBackend::tree,
                "bulk remains pinned to tree");
        std::size_t arena_bytes = maps.map(Tier::bulk)->arena_bytes();
        for (std::size_t t = 0; t < 2; ++t) {
            const auto tier = static_cast<Tier>(t);
            const auto* map = maps.map(tier);
            const auto expected_backend = t == 0 ? options.account_top : options.storage_top;
            require(map->backend() == expected_backend &&
                    std::string(map->backend_name()) == page_backend_name(expected_backend),
                    "configured top backend is reported");
            require(map->capacity() >= capacities[t], "top backend rounds capacity upward");
            arena_bytes += map->arena_bytes();

            const auto first = image.pages[t].size();
            Page appended{};
            for (std::size_t i = 0; i < appended.size(); ++i)
                appended[i] = static_cast<std::uint8_t>(1 + i * 7 + t);
            const auto before_append = map->access_count();
            maps.write_pages_batch(tier, first, {appended});
            maps.write_pages_batch(tier, first + 2, {appended});
            maps.finish_pending_work();
            require(map->access_count() - before_append == 2,
                    "both top backends append through ordinary accesses");
            const auto after_append = map->access_count();
            reject([&] { maps.write_pages_batch(tier, 0, {appended}); },
                   "top-tier dummy overwrite");
            reject([&] { maps.write_pages_batch(tier, first, {appended}); },
                   "top-tier appended page overwrite");
            reject([&] { maps.write_pages_batch(tier, first + 1, {appended}); },
                   "top-tier reserved gap reuse");
            reject([&] { maps.write_pages_batch(tier, capacities[t], {appended}); },
                   "top-tier logical capacity cannot use rounding slack");
            require(map->access_count() == after_append,
                    "invalid top-tier appends perform no map accesses");

            // Twenty lanes cross the default sixteen-lane chunk, preserving
            // duplicate reads and repeated dummy/absent keys across chunks.
            std::array<std::uint64_t, 20> ids{};
            std::array<Page, 20> expected{}, output{};
            std::array<std::uint8_t, 20> expected_found{}, found{};
            const std::array<std::uint64_t, 5> pattern{1, first, 0, first + 1, first + 2};
            for (std::size_t i = 0; i < ids.size(); ++i) {
                ids[i] = pattern[i % pattern.size()];
                expected[i] = i % 5 == 0 ? image.pages[t][1] :
                              i % 5 == 1 || i % 5 == 4 ? appended : Page{};
                expected_found[i] = i % 5 == 3 ? 0 : 1;
                output[i].fill(0xff);
            }
            maps.read_pages_batch(tier, ids.size(), ids.data(), output.data(), found.data());
            require(output == expected && found == expected_found,
                    "mixed top backends preserve duplicate, dummy and missing lanes");
            require(map->access_count() - after_append == ids.size() &&
                    maps.calls()[t] == 1 && maps.accesses()[t] == ids.size(),
                    "top backend counters account for every read lane");
        }
        require(maps.arena_bytes() == arena_bytes && arena_bytes > 0,
                "arena bill includes selected top backends and tree bulk");
    }

    const TieredPageMapOptions hierarchical{PageBackend::hierarchical,
                                          PageBackend::hierarchical};
    TieredPageMaps snapshot_maps(pack_snapshot(snapshot, TierProfile{3, 3}), 1,
                                 hierarchical);
    TieredPageMaps generation_maps(image, 1, hierarchical);
    require(snapshot_maps.map(Tier::account_top)->backend() == PageBackend::hierarchical &&
            generation_maps.map(Tier::storage_top)->backend() == PageBackend::hierarchical,
            "snapshot and inferred-capacity generation constructors accept backends");
}

void test_minimum_hierarchical_capacity() {
    PageMap map({Page{}}, PageBackend::hierarchical);
    require(map.capacity() >= 1, "dummy-only hierarchical map rounds minimum capacity");
    const std::array<PageMap::Key, 3> keys{
        PageMap::encode_key(0), PageMap::encode_key(1), PageMap::encode_key(0)};
    std::array<Page, 3> output{};
    for (auto& page : output) page.fill(0xff);
    std::array<std::uint8_t, 3> found{};
    std::array<cpu_byteslice_oram::BatchRequest, 3> scratch{};
    map.read_pages_batch(keys.size(), keys.data(), output.data(), found.data(), scratch.data());
    require(output == std::array<Page, 3>{} &&
            found == std::array<std::uint8_t, 3>{1, 0, 1},
            "minimum hierarchical map preserves dummy and absent reads");
    require(map.access_count() == 4, "minimum map counts initial load and all reads");
    reject([&] { map.write_pages_batch(1, {Page{}}); },
           "minimum map cannot append into rounded capacity");
}

}  // namespace

int main() {
    try {
        test_capacity_admission();
        test_read_lane_admission();
        test_append_and_preflight();
        test_top_backends();
        test_minimum_hierarchical_capacity();
        std::cout << "MPT append-only and tier-backend ORAM page adapter tests passed\n";
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
