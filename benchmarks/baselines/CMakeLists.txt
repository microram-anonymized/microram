# The baseline workers (README.md in this directory). One build directory per
# baseline, because each needs its own compiler or build type:
#
#   cmake -S benchmarks/baselines -B build-baselines/h2o2ram -DBASELINE=h2o2ram  (GCC)
#   cmake -S benchmarks/baselines -B build-baselines/sonic -DBASELINE=sonic      (Clang)
#
# Sources come from third_party/baselines (fetch.sh). Each worker embeds the
# fetch record, so its hash covers the pinned sources and patches.
cmake_minimum_required(VERSION 3.20)
project(oram_baselines LANGUAGES CXX)

set(BASELINE "" CACHE STRING "h2o2ram or sonic")
set(BASELINES_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../../third_party/baselines" CACHE PATH "fetch.sh destination")
get_filename_component(REPO_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)
get_filename_component(BASELINES_DIR "${BASELINES_DIR}" ABSOLUTE)
if(NOT EXISTS "${BASELINES_DIR}/fetch_record.json")
  message(FATAL_ERROR "no ${BASELINES_DIR}/fetch_record.json; run benchmarks/baselines/fetch.sh")
endif()
# Workers read planner caches beside their executable, so they share bin/.
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
file(READ "${BASELINES_DIR}/fetch_record.json" BASELINE_FETCH_RECORD)
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/fetch_record.hpp.in" "${CMAKE_BINARY_DIR}/generated/fetch_record.hpp" @ONLY)
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${BASELINES_DIR}/fetch_record.json")
find_package(Threads REQUIRED)
enable_testing()

if(BASELINE STREQUAL "h2o2ram")
  if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    message(FATAL_ERROR "H2O2RAM is built with GCC (its CMake and paper); configure with CXX=g++")
  endif()
  find_package(TBB REQUIRED)
  find_package(OpenMP REQUIRED)
  find_package(NLopt REQUIRED)
  find_package(OpenSSL REQUIRED)
  set(H2O2RAM_DIR "${BASELINES_DIR}/h2o2ram")
  # Their CMAKE_CXX_FLAGS_RELEASE, which replaces CMake's (so no -DNDEBUG: their
  # asserts stay on), gnu++20, less the link-time -s. -g changes no code with
  # GCC; the branch census maps instructions to source lines with it.
  set(H2O2RAM_FLAGS -O3 -mavx -mavx512f -mavx512cd -mavx512vl -mavx512bw -mavx512dq -mbmi2 -march=native
      -DPARALLEL -fopenmp -Wno-deprecated-declarations -g)
  set(CMAKE_CXX_FLAGS_RELEASE "")
  file(GLOB H2O2RAM_SOURCES "${H2O2RAM_DIR}/src/*.cpp")
  # One patched tree, two builds: P-H3's and P-H5's flag (H2O2RAM_CONSTANT_TIME_CMOV)
  # only in `h2o2ram`; `h2o2ram_shipped` keeps the published, branching lookups.
  function(h2o2ram_build suffix constant_time)
    add_library(h2o2ram_lib${suffix} STATIC ${H2O2RAM_SOURCES})
    target_include_directories(h2o2ram_lib${suffix} PUBLIC "${H2O2RAM_DIR}/include")
    target_compile_options(h2o2ram_lib${suffix} PUBLIC ${H2O2RAM_FLAGS})
    target_compile_definitions(h2o2ram_lib${suffix} PUBLIC H2O2RAM_FROZEN_PLANNER
        $<$<BOOL:${constant_time}>:H2O2RAM_CONSTANT_TIME_CMOV>)
    set_target_properties(h2o2ram_lib${suffix} PROPERTIES CXX_STANDARD 20 CXX_EXTENSIONS ON)
    target_link_libraries(h2o2ram_lib${suffix} PUBLIC TBB::tbb Threads::Threads OpenMP::OpenMP_CXX
        OpenSSL::Crypto NLopt::nlopt)
  endfunction()
  h2o2ram_build("" TRUE)
  h2o2ram_build("_shipped" FALSE)
  function(h2o2ram_executable name source suffix)
    add_executable(${name} ${source})
    target_include_directories(${name} PRIVATE "${REPO_ROOT}" "${CMAKE_BINARY_DIR}/generated")
    target_link_libraries(${name} PRIVATE h2o2ram_lib${suffix})
    set_target_properties(${name} PROPERTIES CXX_STANDARD 20 CXX_EXTENSIONS ON)
  endfunction()
  h2o2ram_executable(oram_baseline_h2o2ram h2o2ram_worker.cpp "")
  h2o2ram_executable(oram_baseline_h2o2ram_shipped h2o2ram_worker.cpp "_shipped")
  # Counted-allocation builds: the same worker with the counting global
  # allocator and `--allocation-audit 1`; never used for timing.
  h2o2ram_executable(oram_baseline_h2o2ram_audit h2o2ram_worker.cpp "")
  h2o2ram_executable(oram_baseline_h2o2ram_shipped_audit h2o2ram_worker.cpp "_shipped")
  target_compile_definitions(oram_baseline_h2o2ram_audit PRIVATE ORAM_BASELINE_ALLOCATION_AUDIT)
  target_compile_definitions(oram_baseline_h2o2ram_shipped_audit PRIVATE ORAM_BASELINE_ALLOCATION_AUDIT)
  h2o2ram_executable(h2o2ram_index_test tests/h2o2ram_index_test.cpp "")
  h2o2ram_executable(h2o2ram_omap_collision_test tests/h2o2ram_omap_collision_test.cpp "_shipped")
  h2o2ram_executable(h2o2ram_layout_test tests/h2o2ram_layout_test.cpp "")
  h2o2ram_executable(h2o2ram_layout_test_shipped tests/h2o2ram_layout_test.cpp "_shipped")
  # They write a crafted planner cache beside themselves: keep it out of the
  # workers' directory, whose caches campaigns freeze.
  set_target_properties(h2o2ram_layout_test h2o2ram_layout_test_shipped PROPERTIES
      RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin-layout-test")
  h2o2ram_executable(h2o2ram_trace_census tests/h2o2ram_trace_census.cpp "")
  h2o2ram_executable(h2o2ram_trace_census_shipped tests/h2o2ram_trace_census.cpp "_shipped")
  # OHashBucket::build alone (a matched comparator for our routing); the shipped
  # build, since the sorts do not use the patched CMOV.
  h2o2ram_executable(h2o2ram_routing_bench h2o2ram_routing_bench.cpp "_shipped")
  add_test(NAME h2o2ram_index_test COMMAND h2o2ram_index_test)
  add_test(NAME h2o2ram_omap_collision_test COMMAND h2o2ram_omap_collision_test)
  add_test(NAME h2o2ram_layout_test COMMAND h2o2ram_layout_test)
  add_test(NAME h2o2ram_layout_test_shipped COMMAND h2o2ram_layout_test_shipped)
  find_package(Python3 COMPONENTS Interpreter REQUIRED)
  add_test(NAME h2o2ram_worker_test COMMAND "${Python3_EXECUTABLE}"
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/check_h2o2ram_worker.py"
      $<TARGET_FILE:oram_baseline_h2o2ram> $<TARGET_FILE:oram_baseline_h2o2ram_shipped>)
  add_test(NAME h2o2ram_trace_census COMMAND "${Python3_EXECUTABLE}"
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/check_h2o2ram_census.py"
      $<TARGET_FILE:h2o2ram_trace_census> $<TARGET_FILE:h2o2ram_trace_census_shipped>
      $<TARGET_FILE:oram_baseline_h2o2ram>)
  set_tests_properties(h2o2ram_worker_test h2o2ram_trace_census PROPERTIES RUN_SERIAL TRUE)
  # The census writes the planner cache (16, 56 and 1032-byte blocks at 2^16)
  # that these two read; on a fresh build, such as the first one on a target,
  # nothing else has written it yet.
  set_tests_properties(h2o2ram_trace_census PROPERTIES FIXTURES_SETUP h2o2ram_planner_cache)
  set_tests_properties(h2o2ram_omap_collision_test h2o2ram_worker_test PROPERTIES
      FIXTURES_REQUIRED h2o2ram_planner_cache)
elseif(BASELINE STREQUAL "sonic")
  if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    message(FATAL_ERROR "SONIC builds only with Clang; configure with CXX=clang++")
  endif()
  if(NOT CMAKE_BUILD_TYPE STREQUAL "Release")
    message(FATAL_ERROR "SONIC is measured in its README's Release build; configure -DCMAKE_BUILD_TYPE=Release")
  endif()
  # One build, with SONIC's optional AVX-512 primitives on (the artifact's
  # default is off), as for every other system. The demos are not built here (they
  # assume SONIC is the top-level project); run_sonic_pmchain.sh builds sonic_demo
  # in a build directory of its own.
  set(SONIC_ENABLE_AVX512 ON CACHE BOOL "" FORCE)
  set(SONIC_BUILD_APPLICATIONS OFF CACHE BOOL "" FORCE)
  set(SONIC_SOURCE_DIR "${BASELINES_DIR}/sonic/sonic")
  add_subdirectory("${SONIC_SOURCE_DIR}" sonic EXCLUDE_FROM_ALL)
  # SONIC sets its -O3 -march=native and AVX-512 flags per directory: give the
  # worker the same ones, so its inlined SONIC code matches the README build.
  get_directory_property(SONIC_OPTIONS DIRECTORY "${SONIC_SOURCE_DIR}" COMPILE_OPTIONS)
  get_directory_property(SONIC_DEFINITIONS DIRECTORY "${SONIC_SOURCE_DIR}" COMPILE_DEFINITIONS)
  function(sonic_executable name source)
    add_executable(${name} ${source})
    target_include_directories(${name} PRIVATE "${REPO_ROOT}" "${CMAKE_BINARY_DIR}/generated")
    target_compile_options(${name} PRIVATE ${SONIC_OPTIONS})
    target_compile_definitions(${name} PRIVATE ${SONIC_DEFINITIONS})
    target_link_libraries(${name} PRIVATE sonic::oram.native sonic::util Threads::Threads)
    set_target_properties(${name} PROPERTIES CXX_STANDARD 20 CXX_EXTENSIONS OFF)
  endfunction()
  sonic_executable(oram_baseline_sonic sonic_worker.cpp)
  sonic_executable(oram_baseline_sonic_audit sonic_worker.cpp)  # counting allocator
  target_compile_definitions(oram_baseline_sonic_audit PRIVATE ORAM_BASELINE_ALLOCATION_AUDIT)
  sonic_executable(sonic_recursive_map_test tests/sonic_recursive_map_test.cpp)
  sonic_executable(sonic_stress tests/sonic_stress.cpp)  # diagnosis only (P-S1's race), not a test
  add_test(NAME sonic_recursive_map_test COMMAND sonic_recursive_map_test)
  find_package(Python3 COMPONENTS Interpreter REQUIRED)
  add_test(NAME sonic_worker_test COMMAND "${Python3_EXECUTABLE}"
      "${CMAKE_CURRENT_SOURCE_DIR}/tests/check_sonic_worker.py" $<TARGET_FILE:oram_baseline_sonic>)
  set_tests_properties(sonic_worker_test PROPERTIES RUN_SERIAL TRUE)
else()
  message(FATAL_ERROR "set -DBASELINE=h2o2ram (GCC) or -DBASELINE=sonic (Clang)")
endif()
