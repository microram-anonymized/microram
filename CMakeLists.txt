cmake_minimum_required(VERSION 3.16)

project(cpu_byteslice_oram VERSION 0.1.0 LANGUAGES CXX)

# GCC ONLY.  The oblivious kernels depend on GNU inline-asm register
# constraints, and the instruction census and timing test (tests/timing) check
# only the code GCC emits.  Other compilers can lower secret-masked compares
# into memory reads that the census never sees, so they are refused here.
if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  message(FATAL_ERROR
      "cpu_byteslice_oram builds only with GCC (found "
      "${CMAKE_CXX_COMPILER_ID}); configure with CXX=g++")
endif()

# What to build.  One switch for the three combinations anyone actually asks
# for; the two fine-grained switches below stay available for everything else.
#
#   library -- the header-only interface target and its install/export rules,
#              nothing compiled.  This is what a consumer of the library wants,
#              and it is the default when this project is pulled in with
#              add_subdirectory()/FetchContent rather than configured directly.
#   tests   -- library + tests/oram/ (each file its own binary, plus its
#              assert()-live `_checked` twin), registered with CTest.
#   all     -- library + tests + benchmarks/oram/ + the campaign tools in
#              analysis/.  The default when configured at top level.
#
# CPU_BYTESLICE_ORAM_BUILD_TESTS / _BENCHMARKS below override this preset
# within one configured build tree; CHANGING the preset re-derives both of them
# (otherwise the cached value of a switch you set three configures ago would
# quietly win over the preset you just asked for).
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
  set(cpu_byteslice_oram_build_default "all")
else()
  set(cpu_byteslice_oram_build_default "library")
endif()
set(CPU_BYTESLICE_ORAM_BUILD "${cpu_byteslice_oram_build_default}" CACHE STRING
    "What to compile: library (header-only target only) | tests (+ tests) | \
all (+ tests + benchmarks)")
set_property(CACHE CPU_BYTESLICE_ORAM_BUILD PROPERTY STRINGS
    library tests all)

if(CPU_BYTESLICE_ORAM_BUILD STREQUAL "library")
  set(cpu_byteslice_oram_tests_default OFF)
  set(cpu_byteslice_oram_benchmarks_default OFF)
elseif(CPU_BYTESLICE_ORAM_BUILD STREQUAL "tests")
  set(cpu_byteslice_oram_tests_default ON)
  set(cpu_byteslice_oram_benchmarks_default OFF)
elseif(CPU_BYTESLICE_ORAM_BUILD STREQUAL "all")
  set(cpu_byteslice_oram_tests_default ON)
  set(cpu_byteslice_oram_benchmarks_default ON)
else()
  message(FATAL_ERROR
      "CPU_BYTESLICE_ORAM_BUILD=\"${CPU_BYTESLICE_ORAM_BUILD}\" is not one of "
      "library, tests, all.")
endif()

option(CPU_BYTESLICE_ORAM_BUILD_TESTS "Build tests"
    ${cpu_byteslice_oram_tests_default})
option(CPU_BYTESLICE_ORAM_BUILD_BENCHMARKS "Build benchmarks"
    ${cpu_byteslice_oram_benchmarks_default})

# Re-derive the two switches whenever the preset above changes, but never on
# the first configure of a tree -- there the option() defaults already ARE the
# preset's, and forcing would trample a switch passed on that same command
# line.
if(NOT DEFINED CPU_BYTESLICE_ORAM_BUILD_APPLIED)
  set(CPU_BYTESLICE_ORAM_BUILD_APPLIED "${CPU_BYTESLICE_ORAM_BUILD}"
      CACHE INTERNAL "Value of CPU_BYTESLICE_ORAM_BUILD last expanded here")
elseif(NOT CPU_BYTESLICE_ORAM_BUILD STREQUAL CPU_BYTESLICE_ORAM_BUILD_APPLIED)
  set(CPU_BYTESLICE_ORAM_BUILD_TESTS ${cpu_byteslice_oram_tests_default}
      CACHE BOOL "Build tests" FORCE)
  set(CPU_BYTESLICE_ORAM_BUILD_BENCHMARKS
      ${cpu_byteslice_oram_benchmarks_default}
      CACHE BOOL "Build benchmarks" FORCE)
  set(CPU_BYTESLICE_ORAM_BUILD_APPLIED "${CPU_BYTESLICE_ORAM_BUILD}"
      CACHE INTERNAL "Value of CPU_BYTESLICE_ORAM_BUILD last expanded here")
endif()

option(CPU_BYTESLICE_ORAM_SILENCE_LIBC_WARNINGS
    "Silence the fortified-copy diagnostics that glibc's \
<bits/string_fortified.h> raises against OUR inlined calls.  Those wrappers \
are __artificial__, so a warning fired inside one is attributed to the call \
site and -Wno-system-headers does not reach it; when the length is a runtime \
value the compiler cannot fold (a key width chosen at ORAM construction, say) \
it can report a bound it only inferred from a branch it failed to prove dead.  \
Nothing in this project needs it today -- the tree compiles clean without it \
-- so it is here for the next libc that invents one, and turning it OFF is \
the way to see the real thing if you suspect one.  It is applied to this \
project's own test and benchmark binaries only, and never exported to \
consumers of the library." ON)
option(CPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT
    "Use AVX512_VP2INTERSECT for shared key intersections and rebuild key \
deduplication (including Zen 5). Turning it off, or building with a \
compiler that lacks the flag, selects exact online matching and the \
xor + unsigned-min emulation for rebuild intersections." ON)
option(CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT
    "With VP2INTERSECT, match 16-byte stored keys (user keys of 16+ bytes) as \
four 32-bit segments ANDed instead of exactly: faster dedup kernels, at a \
false match probability of at most 2^-104 per compared slot \
(cpu_byteslice_key_intersect.hpp). No effect without VP2INTERSECT." ON)

# Release is the default build type only when this project is configured
# directly.  The cache entry is global, so setting it from an embedded copy
# would change the build type of the whole consuming project.
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR
   AND NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

find_package(Threads REQUIRED)
include(GNUInstallDirs)

add_library(cpu_byteslice_oram INTERFACE)
add_library(cpu_byteslice_oram::cpu_byteslice_oram ALIAS cpu_byteslice_oram)
target_include_directories(cpu_byteslice_oram INTERFACE
    "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
    "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>"
    "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")
target_compile_features(cpu_byteslice_oram INTERFACE cxx_std_17)
target_link_libraries(cpu_byteslice_oram INTERFACE Threads::Threads)

# -march=native asks the compiler to read this machine's actual CPUID and
# enable only what it really has -- unlike hardcoding -mavx512vp2intersect,
# which the compiler accepts as long as it knows the encoding, regardless of
# whether the CPU it's running on can execute it.
# DetectCpuFeatures.cmake double-checks the same CPUID bits independently
# (via __builtin_cpu_supports) so a missing REQUIRED extension is a clear
# configure-time error instead of a runtime SIGILL, and a missing OPTIONAL
# one (VP2INTERSECT) is a performance warning instead of a silent slowdown.
include(cmake/DetectCpuFeatures.cmake)

if(CPU_BYTESLICE_ORAM_FEATURE_PROBE_OK AND CPU_BYTESLICE_ORAM_MISSING_BASELINE)
  message(FATAL_ERROR
      "cpu_byteslice_oram: this CPU is missing required extensions: "
      "${CPU_BYTESLICE_ORAM_MISSING_BASELINE}. The byte-sliced rebuild uses "
      "these unconditionally (no fallback path exists) -- see "
      "README.md#requirements. This "
      "machine cannot build or run this library.")
endif()

# Interface options follow a consumer's private options. Select the checked
# target's optimization here so the normal -O3 cannot override its -O1.
target_compile_options(cpu_byteslice_oram INTERFACE
    "$<IF:$<BOOL:$<TARGET_PROPERTY:CPU_BYTESLICE_ORAM_CHECKED_BUILD>>,-O1,-O3>"
    -march=native)

if(CPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT)
  if(CPU_BYTESLICE_ORAM_FEATURE_PROBE_OK AND NOT CPU_BYTESLICE_ORAM_HAS_VP2INTERSECT)
    message(WARNING
        "cpu_byteslice_oram: this CPU does not support AVX512-VP2INTERSECT "
        "(Tiger Lake and Zen 5 have it; Zen 4 and the Intel server parts "
        "do not). The rebuild's cross-bucket key dedup will use a correct "
        "but slower xor + unsigned-min emulation, and the batch path does "
        "not use its dense cross-match; measure this CPU. Pass "
        "-DCPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT=OFF to silence this "
        "warning once you've accounted for the slowdown.")
  endif()
else()
  # Force it off even on hardware that has it -- e.g. to exercise the
  # emulation path in tests on a VP2INTERSECT-capable machine.
  target_compile_options(cpu_byteslice_oram INTERFACE -mno-avx512vp2intersect)
endif()
if(NOT CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT)
  target_compile_definitions(cpu_byteslice_oram INTERFACE
      MICRORAM_BYTESLICE_WIDE_KEY_VP2INTERSECT=0)
endif()

if(WIN32)
  # MinGW GCC emits aligned 32-byte vmovdqa spills (e.g. for by-value
  # TableView copies) into frames it only keeps 16-byte aligned, so runs
  # crash with 0xC0000005 whenever the randomized thread-stack base leaves
  # rsp at the wrong parity mod 32.  Encode all aligned vector moves as
  # their unaligned forms (identical performance on aligned addresses).
  target_compile_options(cpu_byteslice_oram INTERFACE
      -Wa,-muse-unaligned-vector-move)
endif()

function(cpu_byteslice_oram_add_executable target_name source_path)
  add_executable(${target_name} "${source_path}")
  target_link_libraries(${target_name} PRIVATE cpu_byteslice_oram)
  if(CPU_BYTESLICE_ORAM_SILENCE_LIBC_WARNINGS)
    target_compile_options(${target_name} PRIVATE
        -Wno-stringop-overread -Wno-stringop-overflow)
  endif()
endfunction()

if(CPU_BYTESLICE_ORAM_BUILD_TESTS)
  include(CTest)
  # The online batch primitives must compile and run independently of both
  # optional conflict algorithms (AVX512CD, VP2INTERSECT), even when
  # -march=native enables them.
  # Source options are appended AFTER the interface's architecture flags.
  # On a host with AVX10.1 (Granite Rapids outside a TD), -march=native turns
  # it on, and it implies AVX512CD, so it must go first.  Only there: GCC 15
  # warns about -mno-avx10.1 on every host.
  include(CheckCXXSourceCompiles)
  set(CMAKE_REQUIRED_FLAGS -march=native)
  check_cxx_source_compiles("
#ifndef __AVX10_1__
#error no AVX10.1
#endif
int main() { return 0; }" CPU_BYTESLICE_ORAM_NATIVE_AVX10_1)
  unset(CMAKE_REQUIRED_FLAGS)
  set(CPU_BYTESLICE_ORAM_NO_CONFLICT_ISA "-mno-avx512cd;-mno-avx512vp2intersect")
  if(CPU_BYTESLICE_ORAM_NATIVE_AVX10_1)
    list(PREPEND CPU_BYTESLICE_ORAM_NO_CONFLICT_ISA "-mno-avx10.1")
  endif()
  set_source_files_properties(tests/oram/cpu_byteslice_parallel_batch_test.cpp
      PROPERTIES COMPILE_OPTIONS "${CPU_BYTESLICE_ORAM_NO_CONFLICT_ISA}")
  file(GLOB CPU_BYTESLICE_ORAM_TEST_SOURCES CONFIGURE_DEPENDS
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/oram/*.cpp")
  foreach(source_path IN LISTS CPU_BYTESLICE_ORAM_TEST_SOURCES)
    get_filename_component(target_name "${source_path}" NAME_WE)
    cpu_byteslice_oram_add_executable("${target_name}" "${source_path}")
    set_target_properties(${target_name} PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/tests")
    add_test(NAME ${target_name}
        COMMAND ${target_name}
        WORKING_DIRECTORY "${CMAKE_BINARY_DIR}/tests")

    # The same test with assert() LIVE.  The kernels carry ~60 shape and
    # contract assertions -- "this table is r << block_bits buckets", "an
    # unchecked MergeSplit needs a stash with capacity" -- and the default
    # Release build defines NDEBUG, so without this pass not one of them is
    # ever evaluated.
    #
    # -O1 rather than -O3: the assertions are the point, the wall time is not,
    # and the ORAM tests do real work.
    set(checked_target "${target_name}_checked")
    cpu_byteslice_oram_add_executable("${checked_target}" "${source_path}")
    set_target_properties(${checked_target} PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/tests"
        CPU_BYTESLICE_ORAM_CHECKED_BUILD TRUE)
    target_compile_options(${checked_target} PRIVATE -UNDEBUG)
    add_test(NAME ${checked_target}
        COMMAND ${checked_target}
        WORKING_DIRECTORY "${CMAKE_BINARY_DIR}/tests")
  endforeach()

  # The segment-matched 16-byte keys replace the exact wide path in the main
  # build of a VP2INTERSECT host; these twins keep that exact path tested there.
  if(CPU_BYTESLICE_ORAM_ENABLE_VP2INTERSECT AND
     CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT)
    foreach(test_name cpu_byteslice_dedup_rebuild_test
            cpu_byteslice_dedup_nest_equivalence_test
            cpu_byteslice_batch_match_test)
      set(exact_target "${test_name}_exact_wide")
      cpu_byteslice_oram_add_executable("${exact_target}"
          "${CMAKE_CURRENT_SOURCE_DIR}/tests/oram/${test_name}.cpp")
      set_target_properties(${exact_target} PROPERTIES
          RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/tests")
      target_compile_definitions(${exact_target} PRIVATE
          MICRORAM_BYTESLICE_WIDE_KEY_VP2INTERSECT=0)
      add_test(NAME ${exact_target}
          COMMAND ${exact_target}
          WORKING_DIRECTORY "${CMAKE_BINARY_DIR}/tests")
    endforeach()
  endif()

  # The certification report's hash-cycle guard scans the certification
  # probes' sources, so it needs to know where they are.
  foreach(certification_target cpu_byteslice_level_arena_certification_test
          cpu_byteslice_level_arena_certification_test_checked)
    if(TARGET ${certification_target})
      target_compile_definitions(${certification_target} PRIVATE
          CPU_BYTESLICE_ORAM_SOURCE_DIR="${CMAKE_CURRENT_SOURCE_DIR}")
    endif()
  endforeach()

  # A measurement rather than a functional test: does each instruction the
  # library applies to secret operands take the same time for every operand
  # value on this host (tests/timing/README.md)?  CTest runs the quick smoke
  # mode -- a few seconds, failing only on a leak or a broken instrument --
  # alone on the machine; the certification run is
  # `avx512_constant_time_test --certify`.  The kernels are GNU inline asm.
  cpu_byteslice_oram_add_executable(avx512_constant_time_test
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/timing/avx512_constant_time_test.cpp")
  set_target_properties(avx512_constant_time_test PROPERTIES
      RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/tests")
  add_test(NAME avx512_constant_time_test
      COMMAND avx512_constant_time_test
      WORKING_DIRECTORY "${CMAKE_BINARY_DIR}/tests")
  set_tests_properties(avx512_constant_time_test PROPERTIES
      RUN_SERIAL TRUE
      LABELS timing)

  # The instruction census (tests/timing/instruction_census.py) needs line
  # tables, so it is opt-in: this compiles every test binary with -g1 (line
  # tables only; the generated code is the same) and runs the census over
  # them.  The benchmarks are censused by hand (tests/timing/README.md).
  option(CPU_BYTESLICE_ORAM_INSTRUCTION_CENSUS
      "Build the tests with -g1 and add the instruction census to CTest" OFF)
  if(CPU_BYTESLICE_ORAM_INSTRUCTION_CENSUS)
    find_package(Python3 REQUIRED COMPONENTS Interpreter)
    get_property(census_targets DIRECTORY PROPERTY BUILDSYSTEM_TARGETS)
    list(FILTER census_targets INCLUDE REGEX "^cpu_")
    set(census_binaries "")
    foreach(census_target IN LISTS census_targets)
      get_target_property(census_type ${census_target} TYPE)
      if(census_type STREQUAL "EXECUTABLE")
        target_compile_options(${census_target} PRIVATE -g1)
        list(APPEND census_binaries "$<TARGET_FILE:${census_target}>")
      endif()
    endforeach()
    add_test(NAME instruction_census
        COMMAND "${Python3_EXECUTABLE}"
            "${CMAKE_CURRENT_SOURCE_DIR}/tests/timing/instruction_census.py"
            ${census_binaries}
            --timing-test "$<TARGET_FILE:avx512_constant_time_test>"
            --repo "${CMAKE_CURRENT_SOURCE_DIR}")
    set_tests_properties(instruction_census PROPERTIES LABELS census TIMEOUT 3600)
  endif()

  # CPU_BYTESLICE_ORAM_RELEASE must refuse every instrumentation macro
  # (src/core/release_guard.hpp).  A refused build cannot be a test binary,
  # so this one runs the preprocessor itself.
  add_test(NAME cpu_byteslice_release_guard_refusals
      COMMAND ${CMAKE_COMMAND}
          "-DCXX=${CMAKE_CXX_COMPILER}"
          "-DSOURCE_DIR=${CMAKE_CURRENT_SOURCE_DIR}"
          "-DPROBE=${CMAKE_CURRENT_SOURCE_DIR}/tests/release_guard/release_guard_probe.cpp"
          -P "${CMAKE_CURRENT_SOURCE_DIR}/tests/release_guard/check_release_guard.cmake")
endif()

if(CPU_BYTESLICE_ORAM_BUILD_BENCHMARKS)
  add_subdirectory(analysis)
  file(GLOB CPU_BYTESLICE_ORAM_BENCHMARK_SOURCES CONFIGURE_DEPENDS
      "${CMAKE_CURRENT_SOURCE_DIR}/benchmarks/oram/*.cpp")
  foreach(source_path IN LISTS CPU_BYTESLICE_ORAM_BENCHMARK_SOURCES)
    get_filename_component(target_name "${source_path}" NAME_WE)
    cpu_byteslice_oram_add_executable("${target_name}" "${source_path}")
    set_target_properties(${target_name} PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/benchmarks")
  endforeach()
  if(TARGET cpu_byteslice_occupancy_observer)
    # The residual occupancy observer: the globbed driver is compiled
    # with the observer macro (src/oram/levelarena/
    # cpu_byteslice_level_arena_occupancy.hpp), whose hook sees
    # secret-dependent occupancies.  Diagnostic only, never a performance
    # row; refused by CPU_BYTESLICE_ORAM_RELEASE.
    target_compile_definitions(cpu_byteslice_occupancy_observer PRIVATE
        MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER=1)
  endif()
  if(TARGET cpu_byteslice_level_arena_benchmark)
    # The benchmark-only rebuild-service throttle: the same source with
    # the owner pause points compiled in (src/oram/levelarena/
    # cpu_byteslice_level_arena_pause.hpp), so `--rebuild-slowdown K` can slow
    # every owner thread.  A SEPARATE binary, so the production benchmark keeps
    # the pause points compiled out; refused by CPU_BYTESLICE_ORAM_RELEASE.
    cpu_byteslice_oram_add_executable(
        cpu_byteslice_level_arena_benchmark_throttled
        "${CMAKE_CURRENT_SOURCE_DIR}/benchmarks/oram/cpu_byteslice_level_arena_benchmark.cpp")
    set_target_properties(cpu_byteslice_level_arena_benchmark_throttled
        PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/benchmarks")
    target_compile_definitions(cpu_byteslice_level_arena_benchmark_throttled
        PRIVATE MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE=1)
  endif()
  if(TARGET cpu_byteslice_level_arena_benchmark)
    # The merge comparison counters (MICRORAM_BYTESLICE_COMPARE_COUNT,
    # src/oram/rebuild/cpu_byteslice_compare_count.hpp): the same source
    # printing COMPARE_COUNT, the window's comparisons by kind.  Its timings
    # carry the counters' cost; take merge times from the plain build.
    cpu_byteslice_oram_add_executable(
        cpu_byteslice_level_arena_benchmark_compare_counted
        "${CMAKE_CURRENT_SOURCE_DIR}/benchmarks/oram/cpu_byteslice_level_arena_benchmark.cpp")
    set_target_properties(cpu_byteslice_level_arena_benchmark_compare_counted
        PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/benchmarks")
    target_compile_definitions(cpu_byteslice_level_arena_benchmark_compare_counted
        PRIVATE MICRORAM_BYTESLICE_COMPARE_COUNT=1)
  endif()
  if(TARGET cpu_tree_oram_benchmark)
    # The tree's position-map phase timer: the same source with three clock
    # reads per tree access compiled in (MICRORAM_TREE_PHASE_TIMER,
    # src/oram/tree/cpu_tree_map.hpp), so mode 0 splits each read into its
    # position-map and tree phases.  A separate binary keeps the clocks out of
    # every other build; refused by CPU_BYTESLICE_ORAM_RELEASE.
    cpu_byteslice_oram_add_executable(
        cpu_tree_oram_benchmark_phase_timed
        "${CMAKE_CURRENT_SOURCE_DIR}/benchmarks/oram/cpu_tree_oram_benchmark.cpp")
    set_target_properties(cpu_tree_oram_benchmark_phase_timed
        PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/benchmarks")
    target_compile_definitions(cpu_tree_oram_benchmark_phase_timed
        PRIVATE MICRORAM_TREE_PHASE_TIMER=1)
  endif()
  set(MICRORAM_ENIGMAP_DIR "" CACHE PATH
      "EnigMap checkout (benchmarks/baselines/fetch_enigmap.sh) for the eviction comparator's enigmap arm")
  if(TARGET cpu_tree_eviction_comparator_benchmark AND MICRORAM_ENIGMAP_DIR)
    # The tree eviction comparator with EnigMap's EvictPath beside the read
    # path on the same inputs: the same source with EnigMap's headers, a
    # separate binary so the default build needs no third-party code.
    # EnigMap is C++20, and its headers trip GCC 15's -Wtemplate-body (a
    # member it never instantiates).
    cpu_byteslice_oram_add_executable(
        cpu_tree_eviction_comparator_benchmark_enigmap
        "${CMAKE_CURRENT_SOURCE_DIR}/benchmarks/oram/cpu_tree_eviction_comparator_benchmark.cpp")
    set_target_properties(cpu_tree_eviction_comparator_benchmark_enigmap
        PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/benchmarks" CXX_STANDARD 20)
    target_include_directories(cpu_tree_eviction_comparator_benchmark_enigmap SYSTEM
        PRIVATE "${MICRORAM_ENIGMAP_DIR}/ods")
    target_compile_definitions(cpu_tree_eviction_comparator_benchmark_enigmap
        PRIVATE MICRORAM_ENIGMAP_ARM=1)
    target_compile_options(cpu_tree_eviction_comparator_benchmark_enigmap
        PRIVATE -Wno-template-body)
  endif()
endif()

include(CMakePackageConfigHelpers)

install(TARGETS cpu_byteslice_oram
    EXPORT cpu_byteslice_oramTargets)
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
    DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}")
# Internal implementation headers retain their src/... include paths so both
# source-tree and installed consumers compile the exact same header graph.
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/src/"
    DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/src"
    FILES_MATCHING PATTERN "*.hpp" PATTERN "*.inc")
install(EXPORT cpu_byteslice_oramTargets
    FILE cpu_byteslice_oramTargets.cmake
    NAMESPACE cpu_byteslice_oram::
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/cmake/cpu_byteslice_oram")

configure_package_config_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cpu_byteslice_oramConfig.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cpu_byteslice_oramConfig.cmake"
    INSTALL_DESTINATION "${CMAKE_INSTALL_LIBDIR}/cmake/cpu_byteslice_oram")
write_basic_package_version_file(
    "${CMAKE_CURRENT_BINARY_DIR}/cpu_byteslice_oramConfigVersion.cmake"
    VERSION "${PROJECT_VERSION}"
    COMPATIBILITY SameMajorVersion)
install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/cpu_byteslice_oramConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/cpu_byteslice_oramConfigVersion.cmake"
    DESTINATION "${CMAKE_INSTALL_LIBDIR}/cmake/cpu_byteslice_oram")
