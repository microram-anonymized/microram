# Ethereum MPT proof-service example (see README.md and DESIGN.md here). It is
# example-local code built on the installed library's public API; it adds no
# library API. One public page width applies to every target in a build.
set(ETHEREUM_MPT_PAGE_BYTES "1024" CACHE STRING "Ethereum MPT packed page width in bytes")
set_property(CACHE ETHEREUM_MPT_PAGE_BYTES PROPERTY STRINGS 768 1024 2048)
if(NOT ETHEREUM_MPT_PAGE_BYTES MATCHES "^(768|1024|2048)$")
  message(FATAL_ERROR "ETHEREUM_MPT_PAGE_BYTES must be 768, 1024, or 2048")
endif()

add_library(ethereum_mpt_reference STATIC codec.cpp trie.cpp packing.cpp mock_chain.cpp)
target_include_directories(ethereum_mpt_reference PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}")
target_compile_features(ethereum_mpt_reference PUBLIC cxx_std_17)
target_compile_options(ethereum_mpt_reference PRIVATE -Wall -Wextra -Wpedantic)
target_compile_definitions(ethereum_mpt_reference PUBLIC
    ETHEREUM_MPT_PAGE_BYTES=${ETHEREUM_MPT_PAGE_BYTES})

add_library(ethereum_mpt_traversal STATIC fixed.cpp fixed_node.cpp traversal.cpp)
target_link_libraries(ethereum_mpt_traversal PUBLIC ethereum_mpt_reference)
target_compile_options(ethereum_mpt_traversal PRIVATE -Wall -Wextra -Wpedantic)

add_library(ethereum_mpt_versions STATIC version.cpp checkpoint.cpp)
target_link_libraries(ethereum_mpt_versions PUBLIC ethereum_mpt_traversal)
target_compile_options(ethereum_mpt_versions PRIVATE -Wall -Wextra -Wpedantic)

add_library(ethereum_mpt_client STATIC client.cpp client_verify.cpp)
target_link_libraries(ethereum_mpt_client PUBLIC ethereum_mpt_traversal)
target_compile_options(ethereum_mpt_client PRIVATE -Wall -Wextra -Wpedantic)

# OpenSSL is optional: only the TLS demo and its tests need it.
option(ETHEREUM_MPT_ENABLE_TLS "Build the optional OpenSSL TLS 1.3 MPT transport" OFF)
if(ETHEREUM_MPT_ENABLE_TLS)
  if(NOT UNIX)
    message(FATAL_ERROR "The MPT TLS example requires POSIX sockets")
  endif()
  include(CheckCXXSymbolExists)
  check_cxx_symbol_exists(MSG_NOSIGNAL "sys/socket.h" ETHEREUM_MPT_HAS_MSG_NOSIGNAL)
  if(NOT ETHEREUM_MPT_HAS_MSG_NOSIGNAL)
    message(FATAL_ERROR "The MPT TLS example requires MSG_NOSIGNAL socket writes")
  endif()
  find_package(OpenSSL 3.0 REQUIRED COMPONENTS SSL Crypto)
  find_package(Threads REQUIRED)
  add_library(ethereum_mpt_transport STATIC transport.cpp)
  target_link_libraries(ethereum_mpt_transport PUBLIC ethereum_mpt_client
      OpenSSL::SSL OpenSSL::Crypto)
  target_compile_options(ethereum_mpt_transport PRIVATE -Wall -Wextra -Wpedantic)
  add_executable(ethereum_mpt_tls_demo transport_main.cpp)
  target_link_libraries(ethereum_mpt_tls_demo PRIVATE ethereum_mpt_transport
      Threads::Threads cpu_byteslice_oram::cpu_byteslice_oram)
  target_compile_options(ethereum_mpt_tls_demo PRIVATE -Wall -Wextra -Wpedantic)
endif()

add_executable(ethereum_mpt_example main.cpp)
target_link_libraries(ethereum_mpt_example PRIVATE ethereum_mpt_client
    cpu_byteslice_oram::cpu_byteslice_oram)

add_executable(ethereum_mpt_benchmark benchmark.cpp)
target_link_libraries(ethereum_mpt_benchmark PRIVATE ethereum_mpt_client
    cpu_byteslice_oram::cpu_byteslice_oram)
target_compile_options(ethereum_mpt_benchmark PRIVATE -Wall -Wextra -Wpedantic)

add_executable(ethereum_mpt_update_benchmark update_benchmark.cpp)
target_link_libraries(ethereum_mpt_update_benchmark PRIVATE ethereum_mpt_versions
    ethereum_mpt_client cpu_byteslice_oram::cpu_byteslice_oram)
target_compile_options(ethereum_mpt_update_benchmark PRIVATE -Wall -Wextra -Wpedantic)

add_executable(ethereum_mpt_updates update_main.cpp)
target_link_libraries(ethereum_mpt_updates PRIVATE ethereum_mpt_versions ethereum_mpt_client
    cpu_byteslice_oram::cpu_byteslice_oram)
target_compile_definitions(ethereum_mpt_updates PRIVATE
    ETHEREUM_MPT_BLOCK_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mock_blocks.txt")

add_executable(ethereum_mpt_incremental update_main.cpp)
target_link_libraries(ethereum_mpt_incremental PRIVATE ethereum_mpt_versions ethereum_mpt_client
    cpu_byteslice_oram::cpu_byteslice_oram)
target_compile_definitions(ethereum_mpt_incremental PRIVATE ETHEREUM_MPT_INCREMENTAL
    ETHEREUM_MPT_BLOCK_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mock_blocks.txt")

if(BUILD_TESTING)
  find_package(Python3 COMPONENTS Interpreter QUIET)
  if(ETHEREUM_MPT_ENABLE_TLS)
    add_executable(ethereum_mpt_transport_test transport_test.cpp)
    target_link_libraries(ethereum_mpt_transport_test PRIVATE ethereum_mpt_transport
        Threads::Threads)
    target_compile_options(ethereum_mpt_transport_test PRIVATE -Wall -Wextra -Wpedantic)
    find_program(ETHEREUM_MPT_OPENSSL_EXECUTABLE openssl)
    if(Python3_Interpreter_FOUND AND ETHEREUM_MPT_OPENSSL_EXECUTABLE)
      add_test(NAME ethereum_mpt_transport
          COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/transport_test.py"
                  "$<TARGET_FILE:ethereum_mpt_transport_test>"
                  "$<TARGET_FILE:ethereum_mpt_tls_demo>" "${ETHEREUM_MPT_OPENSSL_EXECUTABLE}")
      set_tests_properties(ethereum_mpt_transport PROPERTIES TIMEOUT 120)
    else()
      message(WARNING "MPT TLS tests require Python3 and the openssl executable")
    endif()
  endif()
  if(Python3_Interpreter_FOUND)
    add_test(NAME ethereum_mpt_benchmark
        COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/benchmark_test.py"
                "$<TARGET_FILE:ethereum_mpt_benchmark>")
    add_test(NAME ethereum_mpt_benchmark_sweep
        COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/benchmark_sweep_test.py")
    add_test(NAME ethereum_mpt_update_benchmark
        COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/update_benchmark_test.py"
                "$<TARGET_FILE:ethereum_mpt_update_benchmark>")
    add_test(NAME ethereum_mpt_update_benchmark_sweep
        COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/update_benchmark_sweep_test.py")
    add_test(NAME ethereum_mpt_checkpoint_cli
        COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/checkpoint_cli_test.py"
                "$<TARGET_FILE:ethereum_mpt_updates>" "$<TARGET_FILE:ethereum_mpt_incremental>"
                "$<TARGET_FILE:ethereum_mpt_checkpoint_test>")
  endif()
  add_executable(ethereum_mpt_client_test client_test.cpp)
  target_link_libraries(ethereum_mpt_client_test PRIVATE ethereum_mpt_client)
  add_test(NAME ethereum_mpt_client COMMAND ethereum_mpt_client_test)
  add_executable(ethereum_mpt_reference_test reference_test.cpp codec_test.cpp trie_test.cpp
      trie_update_test.cpp packing_test.cpp mock_chain_test.cpp canonical_update_test.cpp)
  target_link_libraries(ethereum_mpt_reference_test PRIVATE ethereum_mpt_reference)
  target_compile_definitions(ethereum_mpt_reference_test PRIVATE
      ETHEREUM_MPT_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/oracle_vectors.txt"
      ETHEREUM_MPT_BLOCK_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mock_blocks.txt")
  add_test(NAME ethereum_mpt_reference COMMAND ethereum_mpt_reference_test)
  add_executable(ethereum_mpt_traversal_test traversal_test_main.cpp fixed_test.cpp
      fixed_node_test.cpp traversal_test.cpp)
  target_link_libraries(ethereum_mpt_traversal_test PRIVATE ethereum_mpt_traversal)
  add_test(NAME ethereum_mpt_traversal COMMAND ethereum_mpt_traversal_test)
  add_test(NAME ethereum_mpt_oram_pages COMMAND ethereum_mpt_example)
  add_executable(ethereum_mpt_version_test version_test.cpp)
  target_link_libraries(ethereum_mpt_version_test PRIVATE ethereum_mpt_versions)
  add_test(NAME ethereum_mpt_versions COMMAND ethereum_mpt_version_test)
  add_executable(ethereum_mpt_checkpoint_test checkpoint_test.cpp)
  target_link_libraries(ethereum_mpt_checkpoint_test PRIVATE ethereum_mpt_versions)
  target_compile_definitions(ethereum_mpt_checkpoint_test PRIVATE
      ETHEREUM_MPT_BLOCK_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mock_blocks.txt")
  add_test(NAME ethereum_mpt_checkpoints COMMAND ethereum_mpt_checkpoint_test)
  add_test(NAME ethereum_mpt_oram_updates COMMAND ethereum_mpt_updates)
  add_executable(ethereum_mpt_page_map_test page_map_test.cpp)
  target_link_libraries(ethereum_mpt_page_map_test PRIVATE ethereum_mpt_traversal
      cpu_byteslice_oram::cpu_byteslice_oram)
  add_test(NAME ethereum_mpt_oram_appends COMMAND ethereum_mpt_page_map_test)
  add_executable(ethereum_mpt_incremental_test incremental_test.cpp)
  target_link_libraries(ethereum_mpt_incremental_test PRIVATE ethereum_mpt_versions)
  target_compile_definitions(ethereum_mpt_incremental_test PRIVATE
      ETHEREUM_MPT_BLOCK_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mock_blocks.txt")
  add_test(NAME ethereum_mpt_incremental COMMAND ethereum_mpt_incremental_test)
  add_test(NAME ethereum_mpt_oram_incremental COMMAND ethereum_mpt_incremental)
endif()
