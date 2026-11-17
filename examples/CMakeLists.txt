# Example consumers of the installed library (find_package), built separately
# from the library itself: basic.cpp and the Ethereum MPT example.
cmake_minimum_required(VERSION 3.16)
project(cpu_byteslice_oram_example LANGUAGES CXX)

# Release by default, as for the library and the commands in
# ethereum_mpt/README.md; the demos' test timeouts are sized for it.
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR
   AND NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

find_package(cpu_byteslice_oram CONFIG REQUIRED)

add_executable(cpu_byteslice_oram_example basic.cpp)
target_link_libraries(cpu_byteslice_oram_example
    PRIVATE cpu_byteslice_oram::cpu_byteslice_oram)
target_compile_features(cpu_byteslice_oram_example PRIVATE cxx_std_17)

include(CTest)
add_subdirectory(ethereum_mpt)
