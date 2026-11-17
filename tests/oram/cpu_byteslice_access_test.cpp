// The read-modify-write callback API (`access(key, callback)`) and the mixed
// batch API (`access_batch`) on every backend: the hierarchical ByteMap in
// both storage modes, the tree map, the hybrid map and the planned maps that
// `make_map` builds.
//
// What it checks:
//   * OBLIVIOUS SCHEDULE.  Each callback overload costs a fixed, public number
//     of scheduled ORAM operations (one value access, or two -- three on the
//     tree -- when the callback may rename the key), whether or not the key is
//     present and whether or not the callback actually changes the key.  The
//     count is a function of the overload only, never of the data.
//   * BUDGETS.  A call that would exceed the access horizon (`max_accesses`)
//     or the allowance of key normalizations (keys of 16 bytes or more are
//     mapped through AES; see cpu_byteslice_key_derivation_test.cpp) is
//     refused BEFORE the callback runs, leaving the map and the remaining
//     budget usable.
//   * CORRECTNESS.  Blind overwrites across many stash flushes and rebuilds
//     resolve to the newest copy; an output-free write batch skips the
//     hierarchy probe while an explicit read-then-write does not; repeated
//     keys inside one batch observe lane order.
//   * EXCEPTION SAFETY with workers.  A callback that throws at or next to a
//     stash-flush boundary leaves source and destination unchanged while the
//     value workers (hierarchy) or payload workers (tree) are still running
//     deferred work.

#include <cpu_byteslice_oram/oram.hpp>

#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <exception>
#include <memory>
#include <stdexcept>
#include <utility>

#include <pthread.h>

namespace {

namespace oram = cpu_byteslice_oram;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::ExpectThrowsAs;

using ByteKey = std::array<uint8_t, 13>;
using ByteValue = std::array<uint8_t, 17>;

ByteKey Key(uint8_t number) {
  ByteKey key{};
  key.front() = number;
  key.back() = static_cast<uint8_t>(number + 100);
  return key;
}

ByteValue Value(uint8_t number) {
  ByteValue value{};
  value.fill(number);
  return value;
}

template <class Map>
uint64_t AccessCount(Map& map) {
  return map.access_count();
}

uint64_t AccessCount(oram::ConfiguredByteMap& map) {
  return map.with_backend([](const auto& backend) {
    return backend.access_count();
  });
}

template <class Map, class Callback>
void CheckAccess(Map& map, uint64_t cost, bool expected_found,
                 Callback&& operation) {
  const uint64_t before = AccessCount(map);
  Expect(std::forward<Callback>(operation)() == expected_found,
         "access returned the wrong original presence");
  Expect(AccessCount(map) - before == cost,
         "access used the wrong number of scheduled operations");
}

template <class Map>
void ExpectByteValue(Map& map, const ByteKey& key, uint8_t expected) {
  ByteValue out{};
  Expect(map.find(key.data(), out.data()), "updated byte key disappeared");
  Expect(out == Value(expected), "updated byte value differs from callback");
}

struct CallbackFailure : std::runtime_error {
  CallbackFailure() : std::runtime_error("injected callback failure") {}
};

template <class Map>
void ExerciseWriteBatch(Map& map) {
  const ByteKey key = Key(20);
  const ByteKey other = Key(21);
  const ByteKey missing = Key(22);
  const ByteValue first = Value(101);
  const ByteValue second = Value(102);
  std::array<ByteValue, 4> outputs{};
  const oram::BatchRequest mixed[] = {
      {oram::BatchOp::kWrite, false, key.data(), first.data(), nullptr},
      {oram::BatchOp::kRead, false, key.data(), nullptr, outputs[0].data()},
      {oram::BatchOp::kWrite, false, key.data(), second.data(), nullptr},
      {oram::BatchOp::kRead, false, key.data(), nullptr, outputs[1].data()},
      {oram::BatchOp::kErase, false, key.data(), nullptr, outputs[2].data()},
      {oram::BatchOp::kRead, false, key.data(), nullptr, outputs[3].data()}};
  const uint64_t before = AccessCount(map);
  map.access_batch(6, mixed, nullptr);
  Expect(AccessCount(map) - before == 6,
         "mixed write batch changed the logical operation count");
  Expect(outputs[0] == first && outputs[1] == second &&
             outputs[2] == second && outputs[3] == Value(0),
         "mixed blind/probed batch did not preserve repeated-key order");

  const oram::BatchRequest read_then_write[] = {
      {oram::BatchOp::kReadThenWrite, false, other.data(), first.data(),
       outputs[0].data()},
      {oram::BatchOp::kReadThenWrite, false, other.data(), second.data(),
       outputs[1].data()}};
  uint8_t found[2] = {99, 99};
  map.access_batch(2, read_then_write, found);
  Expect(found[0] == 0 && found[1] == 1 && outputs[0] == Value(0) &&
             outputs[1] == first,
         "explicit read-then-write batch returned the wrong previous entries");
  ExpectByteValue(map, other, 102);

  ByteValue aliased = Value(103);
  const oram::BatchRequest alias_request{
      oram::BatchOp::kReadThenWrite, false, other.data(), aliased.data(),
      aliased.data()};
  map.access_batch(1, &alias_request, nullptr);
  Expect(aliased == second, "read-then-write batch lost an aliased old output");
  ExpectByteValue(map, other, 103);

  // An output-bearing kWrite still returns the previous entry. Only writes
  // requesting neither old bytes nor presence can omit the hierarchy probe.
  const oram::BatchRequest output_write{
      oram::BatchOp::kWrite, false, other.data(), first.data(), outputs[0].data()};
  map.access_batch(1, &output_write, nullptr);
  Expect(outputs[0] == Value(103), "output-bearing write lost its old value");
  const oram::BatchRequest presence_writes[] = {
      {oram::BatchOp::kWrite, false, other.data(), second.data(), nullptr},
      {oram::BatchOp::kWrite, false, missing.data(), second.data(), nullptr}};
  map.access_batch(2, presence_writes, found);
  Expect(found[0] == 1 && found[1] == 0,
         "presence-bearing writes reported the wrong previous entries");
  ExpectByteValue(map, other, 102);
  ExpectByteValue(map, missing, 102);
}

template <class Map>
void ExerciseByteAccess(Map& map, bool tree) {
  const uint64_t value_cost = tree ? 2 : 1;
  const uint64_t key_cost = tree ? 3 : 2;
  const ByteKey source = Key(1);
  const ByteKey renamed = Key(2);
  const ByteKey occupied = Key(3);
  const ByteKey absent = Key(4);
  const ByteKey inserted = Key(5);
  const ByteKey value_only = Key(6);
  unsigned calls = 0;

  map.write(source.data(), Value(10).data());
  map.insert_or_assign(source.data(), Value(11).data());
  CheckAccess(map, value_cost, true, [&] {
    return map.access(source.data(), [&](uint8_t* value) {
      ++calls;
      Expect(std::equal(value, value + ByteValue{}.size(), Value(11).begin()),
             "byte callback did not receive the latest write");
      std::fill_n(value, ByteValue{}.size(), 12);
    });
  });
  Expect(calls == 1, "value callback was not invoked exactly once");
  ExpectByteValue(map, source, 12);

  CheckAccess(map, value_cost, true, [&] {
    return map.access(source.data(), [&](uint8_t* value, bool found) {
      ++calls;
      Expect(found, "found-aware byte callback lost a hit");
      std::fill_n(value, ByteValue{}.size(), 13);
    });
  });
  CheckAccess(map, key_cost, true, [&] {
    return map.access(source.data(), [&](uint8_t* key, uint8_t* value) {
      ++calls;
      Expect(std::equal(key, key + source.size(), source.begin()),
             "key callback did not receive the queried key");
      std::copy(renamed.begin(), renamed.end(), key);
      std::fill_n(value, ByteValue{}.size(), 23);
    });
  });
  Expect(source == Key(1), "key callback modified the caller's query buffer");
  Expect(!map.contains(source.data()), "renaming left the source key present");
  ExpectByteValue(map, renamed, 23);

  // The key-mutating overload has the same schedule even if it keeps the key.
  CheckAccess(map, key_cost, true, [&] {
    return map.access(renamed.data(), [&](uint8_t* key, uint8_t* value,
                                        bool found) {
      ++calls;
      Expect(found && std::equal(key, key + renamed.size(), renamed.begin()),
             "same-key callback received the wrong input");
      std::fill_n(value, ByteValue{}.size(), 24);
    });
  });
  ExpectByteValue(map, renamed, 24);

  map.write(occupied.data(), Value(90).data());
  CheckAccess(map, key_cost, true, [&] {
    return map.access(renamed.data(), [&](uint8_t* key, uint8_t* value,
                                        bool found) {
      ++calls;
      Expect(found, "rename collision lost the source hit");
      std::copy(occupied.begin(), occupied.end(), key);
      std::fill_n(value, ByteValue{}.size(), 25);
    });
  });
  Expect(!map.contains(renamed.data()), "collision retained the source key");
  ExpectByteValue(map, occupied, 25);

  CheckAccess(map, key_cost, false, [&] {
    return map.access(absent.data(), [&](uint8_t* key, uint8_t* value,
                                       bool found) {
      ++calls;
      Expect(!found, "key-mutating callback reported a missing key present");
      Expect(std::equal(value, value + ByteValue{}.size(), Value(0).begin()),
             "key-mutating miss was not initialized to zero");
      std::copy(inserted.begin(), inserted.end(), key);
      std::fill_n(value, ByteValue{}.size(), 50);
    });
  });
  Expect(!map.contains(absent.data()), "missing source was inserted on rename");
  ExpectByteValue(map, inserted, 50);

  CheckAccess(map, value_cost, false, [&] {
    return map.access(value_only.data(), [&](uint8_t* value, bool found) {
      ++calls;
      Expect(!found, "value callback reported a missing key present");
      Expect(std::equal(value, value + ByteValue{}.size(), Value(0).begin()),
             "value-only miss was not initialized to zero");
      std::fill_n(value, ByteValue{}.size(), 60);
    });
  });
  Expect(calls == 7, "a hit or miss callback ran more than once");

  auto move_only = [increment = std::make_unique<uint8_t>(1)](uint8_t* value) {
    for (size_t i = 0; i < ByteValue{}.size(); ++i) value[i] += *increment;
  };
  CheckAccess(map, value_cost, true, [&] {
    return map.access(value_only.data(), std::move(move_only));
  });
  CheckAccess(map, value_cost, true, [&] {
    return map.Access(value_only.data(), [](uint8_t* value) {
      std::fill_n(value, ByteValue{}.size(), 62);
    });
  });
  ExpectByteValue(map, value_only, 62);

  unsigned throws = 0;
  ExpectThrowsAs<CallbackFailure>([&] {
    map.access(occupied.data(), [&](uint8_t* key, uint8_t* value) {
      ++throws;
      std::copy(inserted.begin(), inserted.end(), key);
      std::fill_n(value, ByteValue{}.size(), 0);
      throw CallbackFailure();
    });
  }, "key callback exception was not propagated");
  ExpectByteValue(map, occupied, 25);
  ExpectByteValue(map, inserted, 50);
  ExpectThrowsAs<CallbackFailure>([&] {
    map.access(value_only.data(), [&](uint8_t* value) {
      ++throws;
      std::fill_n(value, ByteValue{}.size(), 0);
      throw CallbackFailure();
    });
  }, "value callback exception was not propagated");
  ExpectByteValue(map, value_only, 62);
  ExpectThrowsAs<CallbackFailure>([&] {
    map.access(absent.data(), [&](uint8_t* value) {
      ++throws;
      std::fill_n(value, ByteValue{}.size(), 99);
      throw CallbackFailure();
    });
  }, "missing-key callback exception was not propagated");
  Expect(throws == 3, "a throwing callback was invoked more than once");
  Expect(!map.contains(absent.data()), "throwing callback inserted a missing key");

  const uint64_t before_invalid = AccessCount(map);
  // A null read through a volatile: the compiler cannot see it, so it does not
  // warn about the key copies that the null check's throw makes unreachable.
  const uint8_t* volatile null_key = nullptr;
  ExpectThrowsAs<std::invalid_argument>([&] {
    map.access(null_key, [&](uint8_t*) { ++calls; });
  }, "access accepted a null key");
  ExpectThrowsAs<std::invalid_argument>([&] {
    map.Access(null_key, [&](uint8_t*, uint8_t*) { ++calls; });
  }, "Access accepted a null key");
  Expect(AccessCount(map) == before_invalid && calls == 7,
         "invalid access touched the map or invoked the callback");
  ExerciseWriteBatch(map);
  map.finish_pending_work();
}

struct StatefulUpdate {
  unsigned calls = 0;
  void operator()(uint64_t& value) & {
    ++calls;
    ++value;
  }
};

template <class Map>
void ExerciseTypedAccess(Map& map, bool tree) {
  const uint64_t value_cost = tree ? 2 : 1;
  const uint64_t key_cost = tree ? 3 : 2;
  unsigned calls = 0;
  map.write(1, 10);
  map.insert_or_assign(1, 11);
  CheckAccess(map, value_cost, true, [&] {
    return map.access(1, [&](uint64_t& value) {
      ++calls;
      Expect(value == 11, "typed callback did not receive the latest write");
      ++value;
    });
  });
  CheckAccess(map, value_cost, true, [&] {
    return map.access(1, [&](uint64_t& value, bool found) {
      ++calls;
      Expect(found && value == 12, "typed found-aware callback lost the hit");
      ++value;
    });
  });
  const uint64_t query = 1;
  CheckAccess(map, key_cost, true, [&] {
    return map.access(query, [&](uint64_t& key, uint64_t& value) {
      ++calls;
      Expect(key == 1 && value == 13, "typed rename received the wrong input");
      key = 2;
      value = 23;
    });
  });
  Expect(query == 1 && !map.contains(1) && map.at(2) == 23,
         "typed rename did not transfer the entry");
  CheckAccess(map, key_cost, true, [&] {
    return map.access(2, [&](uint64_t& key, uint64_t& value, bool found) {
      ++calls;
      Expect(key == 2 && found, "typed same-key callback lost the hit");
      ++value;
    });
  });
  Expect(map.at(2) == 24, "typed same-key callback lost the update");

  map.write(3, 90);
  CheckAccess(map, key_cost, true, [&] {
    return map.access(2, [&](uint64_t& key, uint64_t& value, bool found) {
      ++calls;
      Expect(found, "typed rename collision lost the source hit");
      key = 3;
      value = 25;
    });
  });
  Expect(!map.contains(2) && map.at(3) == 25,
         "typed rename did not overwrite the destination");
  CheckAccess(map, key_cost, false, [&] {
    return map.access(4, [&](uint64_t& key, uint64_t& value, bool found) {
      ++calls;
      Expect(!found && key == 4 && value == 0,
             "typed rename miss received the wrong input");
      key = 5;
      value = 50;
    });
  });
  Expect(!map.contains(4) && map.at(5) == 50,
         "typed rename miss inserted the wrong key");
  CheckAccess(map, value_cost, false, [&] {
    return map.access(6, [&](uint64_t& value, bool found) {
      ++calls;
      Expect(!found && value == 0, "typed value miss was not zero initialized");
      value = 60;
    });
  });
  Expect(calls == 7, "typed callback was not invoked exactly once per access");

  CheckAccess(map, value_cost, true, [&] {
    return map.access(6, [increment = std::make_unique<uint64_t>(1)](
                             uint64_t& value) { value += *increment; });
  });
  StatefulUpdate stateful;
  CheckAccess(map, value_cost, true, [&] { return map.access(6, stateful); });
  Expect(stateful.calls == 1, "access copied the stateful callback");
  CheckAccess(map, value_cost, true, [&] {
    return map.Access(6, [](uint64_t& value) { ++value; });
  });
  Expect(map.at(6) == 63, "move-only or stateful callback lost an update");

  ExpectThrowsAs<CallbackFailure>([&] {
    map.access(3, [](uint64_t& key, uint64_t& value) {
      key = 5;
      value = 0;
      throw CallbackFailure();
    });
  }, "typed rename exception was not propagated");
  Expect(map.at(3) == 25 && map.at(5) == 50,
         "throwing typed rename changed an entry");
  ExpectThrowsAs<CallbackFailure>([&] {
    map.access(6, [](uint64_t& value) {
      value = 0;
      throw CallbackFailure();
    });
  }, "typed update exception was not propagated");
  Expect(map.at(6) == 63, "throwing typed update changed the entry");

  uint64_t old = 99;
  Expect(map.exchange(6, 70, &old, true) && old == 63 && map.at(6) == 70,
         "typed exchange did not read and replace the value");
  Expect(!map.exchange(7, 71, &old, false) && old == 0 && !map.contains(7),
         "typed conditional exchange inserted a missing key");
  old = 99;
  Expect(!map.exchange(7, 71, &old, true) && old == 0 && map.at(7) == 71,
         "typed inserting exchange mishandled a miss");
  uint64_t aliased = 72;
  Expect(map.exchange(7, aliased, &aliased, true) && aliased == 71 &&
             map.at(7) == 72,
         "typed exchange did not preserve aliased input");
  ExpectThrowsAs<std::invalid_argument>([&] {
    map.exchange(7, 73, nullptr, true);
  }, "typed exchange accepted a null output");
  map.finish_pending_work();
}

oram::Options InlineOptions() {
  oram::Options options;
  options.max_accesses = uint64_t{1} << 24;
  options.deamortized_owner_threads = 0;
  options.deamortized_online_stash_entries = 64;
  return options;
}

template <bool Deamortize>
void TestCallbackNormalizationBudget() {
  // ByteKey is stored verbatim; only keys of 16 bytes or more use AES.
  using WideKey = std::array<uint8_t, 16>;
  const auto widen = [](const ByteKey& key) {
    WideKey wide{};
    std::copy(key.begin(), key.end(), wide.begin());
    return wide;
  };
  const WideKey source = widen(Key(1));
  const WideKey destination = widen(Key(2));
  const ByteValue original = Value(10);
  {
    auto options = InlineOptions();
    options.max_accesses = 37;
    oram::ByteMap<Deamortize> map(128, source.size(), original.size(), options);
    Expect(map.engine().MaxKeyNormalizations() == map.capacity() + 37 &&
               map.engine().KeyNormalizationCount() == 0,
           "map did not forward the default normalization allowance");
  }
  {
    auto options = InlineOptions();
    options.max_accesses = 16;
    options.max_key_normalizations = 2;
    oram::ByteMap<Deamortize> map(128, source.size(), original.size(), options);
    Expect(map.engine().MaxKeyNormalizations() == 2,
           "map did not forward the explicit normalization allowance");
    map.write(source.data(), original.data());
    unsigned calls = 0;
    ExpectThrowsAs<std::overflow_error>([&] {
      map.access(source.data(), [&](uint8_t* key, uint8_t*) {
        ++calls;
        std::copy(destination.begin(), destination.end(), key);
      });
    }, "rename began without both key normalizations available");
    Expect(calls == 0 && map.access_count() == 1 &&
               map.engine().KeyNormalizationCount() == 1 && !map.failed(),
           "normalization refusal invoked the callback or consumed its source");
    // The source must remain live, and the one-query callback can still use
    // the remainder even though the two-query callback was refused.
    Expect(map.access(source.data(), [&](uint8_t* value, bool found) {
      ++calls;
      Expect(found && std::equal(value, value + original.size(), original.begin()),
             "normalization refusal changed the callback source");
      std::fill_n(value, original.size(), uint8_t{11});
    }), "one-query callback could not use the remaining normalization");
    Expect(calls == 1 && map.access_count() == 2 &&
               map.engine().KeyNormalizationCount() == 2 && !map.failed(),
           "value callback used the wrong normalization or access count");
    map.finish_pending_work();
  }
  {
    auto options = InlineOptions();
    options.max_accesses = 16;
    options.max_key_normalizations = 3;
    oram::ByteMap<Deamortize> map(128, source.size(), original.size(), options);
    map.write(source.data(), original.data());
    unsigned calls = 0;
    ExpectThrowsAs<CallbackFailure>([&] {
      map.access(source.data(), [&](uint8_t* key, uint8_t* value) {
        ++calls;
        std::copy(destination.begin(), destination.end(), key);
        std::fill_n(value, original.size(), uint8_t{99});
        throw CallbackFailure();
      });
    }, "throwing rename did not propagate its callback exception");
    Expect(calls == 1 && map.access_count() == 2 &&
               map.engine().KeyNormalizationCount() == 2 && !map.failed(),
           "throwing rename normalized its destination or charged restoration");
    Expect(map.access(source.data(), [&](uint8_t* value, bool found) {
      ++calls;
      Expect(found && std::equal(value, value + original.size(), original.begin()),
             "throwing rename failed to restore its original source");
    }), "callback restoration lost the source");
    Expect(calls == 2 && map.access_count() == 3 &&
               map.engine().KeyNormalizationCount() == 3,
           "throwing rename did not leave its unused normalization available");
    map.finish_pending_work();
  }
  {
    auto options = InlineOptions();
    options.max_accesses = 16;
    options.max_key_normalizations = 0;
    oram::ByteMap<Deamortize> map(128, 8, original.size(), options);
    map.write(source.data(), original.data());
    Expect(map.access(source.data(), [&](uint8_t* key, uint8_t*) {
      std::copy_n(destination.begin(), 8, key);
    }), "narrow rename incorrectly required normalization budget");
    ByteValue out{};
    Expect(map.find(destination.data(), out.data()) && out == original &&
               !map.contains(source.data()) &&
               map.engine().KeyNormalizationCount() == 0 && !map.failed(),
           "zero normalization allowance changed narrow callback semantics");
    map.finish_pending_work();
  }
}

template <bool Deamortize>
void TestCallbackHorizon() {
  const ByteKey source = Key(1);
  const ByteKey destination = Key(2);
  const ByteValue original = Value(10);
  unsigned calls = 0;
  {
    auto options = InlineOptions();
    options.max_accesses = 2;
    oram::ByteMap<Deamortize> map(128, source.size(), original.size(), options);
    map.write(source.data(), original.data());
    ExpectThrowsAs<std::overflow_error>([&] {
      map.access(source.data(), [&](uint8_t* key, uint8_t*) {
        ++calls;
        std::copy(destination.begin(), destination.end(), key);
      });
    }, "hierarchy rename did not reserve both accesses before the callback");
    Expect(calls == 0 && map.access_count() == 1 && !map.failed(),
           "refused hierarchy rename ran the callback or consumed an access");
    // A one-access update can still use the remainder, and must see the
    // original source rather than a tombstone left by the refused rename.
    Expect(map.access(source.data(), [&](uint8_t* value, bool found) {
      ++calls;
      Expect(found && std::equal(value, value + original.size(), original.begin()),
             "refused hierarchy rename changed the source");
    }), "remaining hierarchy callback lost its source");
    Expect(calls == 1 && map.access_count() == 2,
           "remaining hierarchy callback used the wrong horizon cost");
    ByteValue out = Value(99);
    ExpectThrowsAs<std::overflow_error>([&] {
      map.find(source.data(), out.data());
    }, "hierarchy read exceeded the callback horizon");
    Expect(out == Value(99) && !map.failed(),
           "refused hierarchy read changed output or latched failure");
    map.finish_pending_work();
  }
  for (bool changes_key : {false, true}) {
    oram::TreeOptions options;
    options.position_map = InlineOptions();
    options.position_map.max_accesses = changes_key ? 3 : 2;
    options.payload_max_threads = 0;
    oram::TreeByteMap<Deamortize> map(128, source.size(), original.size(), options);
    map.write(source.data(), original.data());
    calls = 0;
    ExpectThrowsAs<std::overflow_error>([&] {
      if (changes_key) {
        map.access(source.data(), [&](uint8_t* key, uint8_t*) {
          ++calls;
          std::copy(destination.begin(), destination.end(), key);
        });
      } else {
        map.access(source.data(), [&](uint8_t*) { ++calls; });
      }
    }, "tree callback began without its complete access budget");
    Expect(calls == 0 && map.access_count() == 1 &&
               map.position_map_access_count() == 1 && !map.failed(),
           "refused tree callback mutated or failed either structure");
    if (changes_key) {
      Expect(map.access(source.data(), [&](uint8_t* value, bool found) {
        ++calls;
        Expect(found && std::equal(value, value + original.size(), original.begin()),
               "refused tree rename changed its source");
      }), "smaller tree callback could not use the remaining two accesses");
    } else {
      ByteValue out{};
      Expect(map.find(source.data(), out.data()) && out == original,
             "refused tree callback changed its source or spent its remainder");
    }
    const uint64_t limit = options.position_map.max_accesses;
    Expect(map.access_count() == limit && map.position_map_access_count() == limit,
           "tree callback horizon counters disagree");
    ByteValue out = Value(99);
    ExpectThrowsAs<std::overflow_error>([&] {
      map.find(source.data(), out.data());
    }, "tree scalar access exceeded its position-map horizon");
    Expect(out == Value(99) && !map.failed() &&
               map.access_count() == limit && map.position_map_access_count() == limit,
           "refused tree scalar access changed output, counters or failure state");
    map.finish_pending_work();
  }
}

template <bool Deamortize>
void TestTreeBatchHorizon() {
  oram::TreeOptions options;
  options.position_map = InlineOptions();
  options.position_map.max_accesses = 3;
  options.payload_max_threads = 0;
  const ByteKey key = Key(1);
  const ByteValue original = Value(10);
  oram::TreeByteMap<Deamortize> map(128, key.size(), original.size(), options);
  map.write(key.data(), original.data());
  std::array<ByteValue, 3> out{Value(99), Value(99), Value(99)};
  const oram::BatchRequest requests[] = {
      {oram::BatchOp::kRead, false, key.data(), nullptr, out[0].data()},
      {oram::BatchOp::kErase, false, key.data(), nullptr, out[1].data()},
      {oram::BatchOp::kRead, false, key.data(), nullptr, out[2].data()}};
  std::array<uint8_t, 3> found{99, 99, 99};
  ExpectThrowsAs<std::overflow_error>([&] {
    map.access_batch(3, requests, found.data());
  }, "tree batch began partial position remapping beyond its horizon");
  Expect(map.access_count() == 1 && map.position_map_access_count() == 1 &&
             !map.failed() && found == std::array<uint8_t, 3>{99, 99, 99} &&
             out == std::array<ByteValue, 3>{Value(99), Value(99), Value(99)},
         "refused tree batch changed state or outputs");
  // The smaller complete batch fits and still observes the original entry.
  map.access_batch(2, requests, found.data());
  Expect(found[0] == 1 && found[1] == 1 && found[2] == 99 &&
             out[0] == original && out[1] == original && out[2] == Value(99) &&
             map.access_count() == 3 && map.position_map_access_count() == 3 &&
             !map.failed(),
         "smaller tree batch did not preserve the original map after refusal");
  map.finish_pending_work();
}

template <bool Deamortize>
void TestBackends() {
  const auto hierarchy_options = InlineOptions();
  oram::TreeOptions tree_options;
  tree_options.position_map = hierarchy_options;
  tree_options.payload_max_threads = 0;
  {
    oram::ByteMap<Deamortize> map(128, ByteKey{}.size(), ByteValue{}.size(),
                                 hierarchy_options);
    ExerciseByteAccess(map, false);
  }
  {
    oram::TreeByteMap<Deamortize> map(128, ByteKey{}.size(), ByteValue{}.size(),
                                     tree_options);
    ExerciseByteAccess(map, true);
  }
  {
    oram::HierarchicalMap<uint64_t, uint64_t, Deamortize> map(
        128, hierarchy_options);
    ExerciseTypedAccess(map, false);
  }
  {
    oram::TreeMap<uint64_t, uint64_t, Deamortize> map(128, tree_options);
    ExerciseTypedAccess(map, true);
  }
  for (bool tree : {false, true}) {
    oram::HybridOptions options(hierarchy_options);
    options.tree = tree_options;
    options.tree_value_threshold = tree ? 1 : 1024;
    oram::HybridByteMap<Deamortize> bytes(
        128, ByteKey{}.size(), ByteValue{}.size(), options);
    ExerciseByteAccess(bytes, tree);
    oram::Map<uint64_t, uint64_t, Deamortize> typed(128, options);
    ExerciseTypedAccess(typed, tree);
  }
}

void TestConfiguredMaps() {
  for (auto scheme : {oram::Scheme::kHierarchicalIncremental,
                      oram::Scheme::kHierarchicalSynchronous,
                      oram::Scheme::kTree}) {
    oram::OptionOverrides overrides;
    overrides.scheme = scheme;
    const auto plan = oram::resolve_options(
        {128, ByteKey{}.size(), ByteValue{}.size()}, {1}, {}, overrides);
    auto map = oram::make_map(plan);
    ExerciseByteAccess(map, scheme == oram::Scheme::kTree);
  }
}

template <bool Deamortize>
void TestBlindOverwriteAcrossRebuilds() {
  oram::HierarchicalMap<uint64_t, uint64_t, Deamortize> map(128, InlineOptions());
  // Repeated writes span many stash flushes and leave older copies below the
  // newest one. Reads and erases must still resolve the newest logical entry.
  for (uint64_t version = 0; version < 2048; ++version) {
    if ((version & 1) == 0) map.write(1, version);
    else map.insert_or_assign(1, version);
  }
  Expect(map.at(1) == 2047, "blind overwrites resurrected an older value");
  Expect(map.erase(1), "erase missed a repeatedly overwritten key");
  for (uint64_t version = 0; version < 1024; ++version) map.write(2, version);
  map.finish_pending_work();
  Expect(!map.contains(1), "rebuild resurrected a blindly overwritten erased key");
  Expect(map.at(2) == 1023, "subsequent blind overwrite lost its latest value");
}

template <bool Deamortize>
void TestBlindBatchSkipsProbe() {
  oram::ByteMap<Deamortize> map(128, ByteKey{}.size(), ByteValue{}.size(),
                               InlineOptions());
  const ByteKey key = Key(1);
  const ByteValue first = Value(1);
  const ByteValue second = Value(2);
  const oram::BatchRequest writes[] = {
      {oram::BatchOp::kWrite, false, key.data(), first.data(), nullptr},
      {oram::BatchOp::kWrite, false, key.data(), second.data(), nullptr}};
  map.access_batch(2, writes, nullptr);
  Expect(map.access_count() == 2 && map.last_probe_tables() == 0 &&
             map.last_probe_buckets() == 0,
         "output-free write batch performed a hierarchy probe");
  const oram::BatchRequest explicit_probe{
      oram::BatchOp::kReadThenWrite, false, key.data(), first.data(), nullptr};
  map.access_batch(1, &explicit_probe, nullptr);
  Expect(map.access_count() == 3 && map.last_probe_tables() > 0,
         "explicit read-then-write batch skipped its hierarchy probe");
  ExpectByteValue(map, key, 1);
  map.finish_pending_work();
}

using WideValue = std::array<uint64_t, 16>;

WideValue Wide(uint64_t version) {
  WideValue value{};
  value.fill(version);
  return value;
}

template <class Map>
void ExerciseWorkerAccess(Map& map) {
  map.write(9, Wide(90));
  for (uint64_t version = 0; version < 256; ++version) {
    map.write(7, Wide(version));
    Expect(map.access(7, [&](WideValue& value) {
      Expect(value == Wide(version), "worker callback read stale payload bytes");
      value.fill(version + 1);
    }), "worker callback lost a present key");
  }
  Expect(map.at(7) == Wide(256), "worker callback failed to commit the payload");

  // Throw immediately before and at a 64-entry stash boundary. Restoration
  // must cooperate with deferred payload and rebuild work just as a
  // successful update does.
  for (unsigned boundary = 0; boundary < 4; ++boundary) {
    while (map.access_count() % 64 != 62) map.write(100, Wide(boundary));
    ExpectThrowsAs<CallbackFailure>([&] {
      map.access(7, [](WideValue& value) {
        value.fill(0);
        throw CallbackFailure();
      });
    }, "worker value callback swallowed an exception");
    ExpectThrowsAs<CallbackFailure>([&] {
      map.access(7, [](uint64_t& key, WideValue& value) {
        key = 9;
        value.fill(0);
        throw CallbackFailure();
      });
    }, "worker key callback swallowed an exception");
    Expect(map.at(7) == Wide(256) && map.at(9) == Wide(90),
           "throwing worker callback changed the source or destination");
    Expect(map.access(7, [](uint64_t& key, WideValue&) { key = 8; }),
           "worker callback could not rename the source");
    Expect(!map.contains(7) && map.at(8) == Wide(256),
           "worker callback rename lost the payload");
    Expect(map.access(8, [](uint64_t& key, WideValue&) { key = 7; }),
           "worker callback could not rename the source back");
  }

  const uint64_t key = 7;
  const auto* key_bytes = reinterpret_cast<const uint8_t*>(&key);
  const WideValue first = Wide(300);
  const WideValue second = Wide(301);
  WideValue first_out{}, second_out{};
  const oram::BatchRequest mixed[] = {
      {oram::BatchOp::kWrite, false, key_bytes,
       reinterpret_cast<const uint8_t*>(first.data()), nullptr},
      {oram::BatchOp::kRead, false, key_bytes, nullptr,
       reinterpret_cast<uint8_t*>(first_out.data())},
      {oram::BatchOp::kWrite, false, key_bytes,
       reinterpret_cast<const uint8_t*>(second.data()), nullptr},
      {oram::BatchOp::kRead, false, key_bytes, nullptr,
       reinterpret_cast<uint8_t*>(second_out.data())}};
  map.byte_map().access_batch(4, mixed, nullptr);
  Expect(first_out == first && second_out == second,
         "mixed blind/probed batch raced with deferred payload work");
  map.finish_pending_work();
  Expect(map.at(7) == second && map.at(9) == Wide(90),
         "draining workers changed committed callback data");
  map.finish_pending_work();
}

void TestWorkerAccess() {
  auto options = InlineOptions();
  options.deamortized_owner_threads = 2;
  options.deamortized_value_workers = 2;
  {
    oram::HierarchicalMap<uint64_t, WideValue> map(128, options);
    Expect(map.byte_map().engine().threaded() &&
               map.byte_map().engine().ValueWorkers() == 2,
           "callback test did not enable hierarchy workers");
    ExerciseWorkerAccess(map);
  }
  {
    oram::TreeOptions tree_options;
    tree_options.position_map = InlineOptions();
    tree_options.payload_max_threads = 2;
    tree_options.payload_threshold = 64;
    oram::TreeMap<uint64_t, WideValue> map(128, tree_options);
    Expect(map.byte_map().payload_planes() == 2,
           "callback test did not enable both tree payload workers");
    ExerciseWorkerAccess(map);
  }
}

// Runs `body` on a thread with a `stack_bytes` stack and rethrows what it
// threw.  A typed value wider than that stack must not be staged on it.
template <class Body>
void OnSmallStack(size_t stack_bytes, Body body) {
  struct Call {
    Body* body;
    std::exception_ptr error;
    static void* Run(void* arg) {
      auto* call = static_cast<Call*>(arg);
      try {
        (*call->body)();
      } catch (...) {
        call->error = std::current_exception();
      }
      return nullptr;
    }
  } call{&body, nullptr};
  pthread_attr_t attr;
  Expect(pthread_attr_init(&attr) == 0 &&
             pthread_attr_setstacksize(&attr, stack_bytes) == 0,
         "cannot size a thread's stack");
  pthread_t thread;
  Expect(pthread_create(&thread, &attr, &Call::Run, &call) == 0,
         "cannot start a small-stack thread");
  pthread_join(thread, nullptr);
  pthread_attr_destroy(&attr);
  if (call.error) std::rethrow_exception(call.error);
}

// THE TYPED ADAPTER STAGES NO WIDE VALUE ON THE CALLER'S STACK.  A tree map
// of 1 MiB values used from a thread with a 512 KiB stack, and a
// hierarchical map of 64 KiB values (bulk initialization included) from a
// 48 KiB one: find, exchange (aliased too) and callback access.  Map, value
// and output live on the heap.
void TestWideTypedValuesOnASmallStack() {
  using Mib = std::array<uint8_t, size_t{1} << 20>;
  static_assert(sizeof(Mib) > oram::kTypedStackValueBytes, "not a wide value");
  oram::TreeOptions tree_options;
  tree_options.payload_max_threads = 0;
  tree_options.position_map.deamortized_owner_threads = 0;
  auto tree = std::make_unique<oram::TreeMap<uint64_t, Mib>>(128, tree_options);
  auto value = std::make_unique<Mib>();
  auto out = std::make_unique<Mib>();
  value->fill(42);
  value->back() = 7;
  tree->write(1, *value);
  OnSmallStack(512 << 10, [&] {
    out->fill(0xAB);
    Expect(tree->find(1, out.get()) && *out == *value,
           "wide typed find returned the wrong value");
    Expect(!tree->find(2, out.get()) &&
               std::all_of(out->begin(), out->end(),
                           [](uint8_t b) { return b == 0; }),
           "wide typed find did not zero the output on a miss");
    value->fill(9);
    Expect(tree->exchange(1, *value, out.get()) && (*out)[0] == 42 &&
               out->back() == 7,
           "wide typed exchange returned the wrong old value");
    *out = *value;
    out->fill(11);
    Expect(tree->exchange(1, *out, out.get()) && (*out)[0] == 9,
           "wide typed exchange with an aliased output failed");
    Expect(tree->access(1, [](Mib& v, bool found) {
             if (found) v[5] = 77;
           }),
           "wide typed access missed");
    Expect(tree->find(1, out.get()) && (*out)[0] == 11 && (*out)[5] == 77,
           "wide typed access lost its update");
  });

  using Wide = std::array<uint8_t, size_t{1} << 16>;
  oram::Options options;
  options.deamortized_top_digit = 1;
  options.deamortized_prefix_flushes = 2;
  auto map = std::make_unique<oram::HierarchicalMap<uint64_t, Wide, false>>(
      256, options);
  auto wide = std::make_unique<Wide>();
  auto wide_out = std::make_unique<Wide>();
  OnSmallStack(48 << 10, [&] {
    struct Record {
      uint64_t first;
      const Wide& second;
    };
    struct Input {
      const Wide* value;
      uint64_t i = 0;
      Record operator*() const { return Record{i + 1, *value}; }
      Input& operator++() {
        ++i;
        return *this;
      }
    };
    wide->fill(5);
    map->initialize(Input{wide.get()}, 3);
    Expect(map->find(2, wide_out.get()) && (*wide_out)[100] == 5,
           "wide typed initialization lost a record");
    wide->fill(6);
    Expect(map->exchange(3, *wide, wide_out.get()) && (*wide_out)[0] == 5,
           "wide typed exchange on the hierarchy failed");
    Expect(map->access(3, [](Wide& v) { v[1] = 8; }),
           "wide typed access on the hierarchy missed");
    Expect(map->find(3, wide_out.get()) && (*wide_out)[0] == 6 &&
               (*wide_out)[1] == 8,
           "wide typed access on the hierarchy lost its update");
  });
  std::puts("  wide typed values on a small stack: tree 1 MiB, hierarchy 64 KiB");
}

}  // namespace

int main() {
  TestCallbackNormalizationBudget<false>();
  TestCallbackNormalizationBudget<true>();
  TestCallbackHorizon<false>();
  TestCallbackHorizon<true>();
  TestTreeBatchHorizon<false>();
  TestTreeBatchHorizon<true>();
  TestBackends<false>();
  TestBackends<true>();
  TestConfiguredMaps();
  TestBlindOverwriteAcrossRebuilds<false>();
  TestBlindOverwriteAcrossRebuilds<true>();
  TestBlindBatchSkipsProbe<false>();
  TestBlindBatchSkipsProbe<true>();
  TestWorkerAccess();
  TestWideTypedValuesOnASmallStack();
  std::puts("cpu_byteslice_access_test: passed");
}
