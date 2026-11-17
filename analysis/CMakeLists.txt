cmake_minimum_required(VERSION 3.16)

# The portable campaign tools: the C++ statistics reducer (oram_bench_aggregate),
# the synthetic one-trial worker and their tests. This directory can be
# configured alone on machines without the ORAM ISA (analysis/oram_bench/WORKER.md).
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
  project(oram_bench_analysis LANGUAGES CXX)
  include(CTest)
  set(oram_bench_test_enabled ${BUILD_TESTING})
else()
  set(oram_bench_test_enabled ${CPU_BYTESLICE_ORAM_BUILD_TESTS})
endif()

add_executable(oram_bench_aggregate oram_bench_aggregate.cpp)
target_compile_features(oram_bench_aggregate PRIVATE cxx_std_17)
target_include_directories(oram_bench_aggregate PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")

find_package(Threads REQUIRED)
add_executable(oram_bench_fake_worker oram_bench_fake_worker.cpp)
target_compile_features(oram_bench_fake_worker PRIVATE cxx_std_17)
target_include_directories(oram_bench_fake_worker PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
target_link_libraries(oram_bench_fake_worker PRIVATE Threads::Threads)

if(oram_bench_test_enabled)
  add_executable(oram_bench_resolver_request_fixture ../tests/analysis/oram_bench_resolver_request_fixture.cpp)
  target_compile_features(oram_bench_resolver_request_fixture PRIVATE cxx_std_17)
  target_include_directories(oram_bench_resolver_request_fixture PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  add_executable(oram_bench_placement_test ../tests/analysis/oram_bench_placement_test.cpp)
  target_compile_features(oram_bench_placement_test PRIVATE cxx_std_17)
  target_include_directories(oram_bench_placement_test PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  target_link_libraries(oram_bench_placement_test PRIVATE Threads::Threads)
  add_test(NAME oram_bench_placement_test COMMAND oram_bench_placement_test)
  add_executable(oram_bench_memory_test ../tests/analysis/oram_bench_memory_test.cpp)
  target_compile_features(oram_bench_memory_test PRIVATE cxx_std_17)
  target_include_directories(oram_bench_memory_test PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  target_link_libraries(oram_bench_memory_test PRIVATE Threads::Threads)
  add_test(NAME oram_bench_memory_test COMMAND oram_bench_memory_test)
  add_executable(oram_bench_worker_test ../tests/analysis/oram_bench_worker_test.cpp)
  target_compile_features(oram_bench_worker_test PRIVATE cxx_std_17)
  target_include_directories(oram_bench_worker_test PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  target_link_libraries(oram_bench_worker_test PRIVATE Threads::Threads)
  add_test(NAME oram_bench_worker_test COMMAND oram_bench_worker_test)
  add_executable(oram_bench_events_test ../tests/analysis/oram_bench_events_test.cpp)
  target_compile_features(oram_bench_events_test PRIVATE cxx_std_17)
  target_include_directories(oram_bench_events_test PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  target_link_libraries(oram_bench_events_test PRIVATE Threads::Threads)
  add_test(NAME oram_bench_events_test COMMAND oram_bench_events_test)
  add_executable(oram_bench_trial_test ../tests/analysis/oram_bench_trial_test.cpp)
  target_compile_features(oram_bench_trial_test PRIVATE cxx_std_17)
  target_include_directories(oram_bench_trial_test PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  add_test(NAME oram_bench_trial_test COMMAND oram_bench_trial_test)
  add_executable(oram_bench_workload_test ../tests/analysis/oram_bench_workload_test.cpp)
  target_compile_features(oram_bench_workload_test PRIVATE cxx_std_17)
  target_include_directories(oram_bench_workload_test PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  add_test(NAME oram_bench_workload_test COMMAND oram_bench_workload_test)
  add_executable(oram_bench_statistics_test ../tests/analysis/oram_bench_statistics_test.cpp)
  target_compile_features(oram_bench_statistics_test PRIVATE cxx_std_17)
  target_include_directories(oram_bench_statistics_test PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/..")
  add_test(NAME oram_bench_statistics_test COMMAND oram_bench_statistics_test)
  find_package(Python3 COMPONENTS Interpreter QUIET)
  if(Python3_Interpreter_FOUND)
    add_test(NAME oram_bench_resolver_request_test
      COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/../tests/analysis/check_resolver_request.py"
        "$<TARGET_FILE:oram_bench_resolver_request_fixture>")
    if(UNIX)
      add_test(NAME oram_bench_campaign_cli_test
        COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/../tests/analysis/check_campaign_cli.py"
          "$<TARGET_FILE:oram_bench_fake_worker>" "$<TARGET_FILE:oram_bench_aggregate>")
    endif()
    add_test(NAME oram_bench_worker_cli_test
      COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/../tests/analysis/check_worker_cli.py"
        "$<TARGET_FILE:oram_bench_fake_worker>" "$<TARGET_FILE:oram_bench_aggregate>")
    add_test(NAME oram_bench_aggregate_cli_test
      COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/../tests/analysis/check_aggregate_cli.py"
        "$<TARGET_FILE:oram_bench_aggregate>" "$<TARGET_FILE:oram_bench_statistics_test>")
  endif()
endif()
