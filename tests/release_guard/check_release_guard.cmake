# Checks src/core/release_guard.hpp by running the preprocessor directly:
#
#   each instrumentation macro ALONE            -> preprocesses cleanly
#   CPU_BYTESLICE_ORAM_RELEASE alone            -> preprocesses cleanly
#   CPU_BYTESLICE_ORAM_RELEASE + each macro     -> fails, naming that macro
#
# The first two rows are the control: they show the command line itself works,
# so a failure in the third row is the guard's and not a bad include path.
#
# Inputs (-D): CXX, SOURCE_DIR, PROBE.

set(macros
    MICRORAM_BYTESLICE_PROBE_AUDIT
    MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
    MICRORAM_BYTESLICE_BATCH_PROFILE
    MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
    MICRORAM_TREE_PHASE_TIMER
    MICRORAM_BYTESLICE_COMPARE_COUNT)

set(base_args -E -std=c++17 -march=native
    "-I${SOURCE_DIR}/include" "-I${SOURCE_DIR}" "${PROBE}")

function(preprocess out_result out_log)
  execute_process(
      COMMAND "${CXX}" ${ARGN} ${base_args}
      RESULT_VARIABLE result
      OUTPUT_QUIET
      ERROR_VARIABLE log)
  set(${out_result} "${result}" PARENT_SCOPE)
  set(${out_log} "${log}" PARENT_SCOPE)
endfunction()

set(failures 0)

preprocess(result log -DCPU_BYTESLICE_ORAM_RELEASE=1)
if(NOT result EQUAL 0)
  message(SEND_ERROR "release macro alone failed to preprocess:\n${log}")
  math(EXPR failures "${failures} + 1")
endif()

foreach(macro IN LISTS macros)
  preprocess(result log "-D${macro}=1")
  if(NOT result EQUAL 0)
    message(SEND_ERROR "${macro} alone failed to preprocess:\n${log}")
    math(EXPR failures "${failures} + 1")
  endif()

  preprocess(result log -DCPU_BYTESLICE_ORAM_RELEASE=1 "-D${macro}=1")
  if(result EQUAL 0)
    message(SEND_ERROR
        "CPU_BYTESLICE_ORAM_RELEASE + ${macro} preprocessed cleanly; the "
        "guard did not fire")
    math(EXPR failures "${failures} + 1")
  elseif(NOT log MATCHES "CPU_BYTESLICE_ORAM_RELEASE: ${macro} is ")
    message(SEND_ERROR
        "CPU_BYTESLICE_ORAM_RELEASE + ${macro} failed, but not with the "
        "guard's message:\n${log}")
    math(EXPR failures "${failures} + 1")
  endif()
endforeach()

if(failures EQUAL 0)
  message(STATUS "release guard: all checks passed")
endif()
