# Checks the *building* machine's real CPUID bits (not just whether the
# compiler accepts a -m flag -- that only proves the compiler knows how to
# encode an instruction, not that this CPU can execute it; an optional
# extension such as AVX512_VP2INTERSECT can be compilable yet raise SIGILL on
# hardware that does not implement it).  The library builds with
# -march=native, so this check only turns a missing required extension into a
# clear configure-time message and reports whether the optional VP2INTERSECT
# path is available.
#
# Sets, in the caller's scope:
#   CPU_BYTESLICE_ORAM_MISSING_BASELINE  -- list of required extensions this
#                                            CPU lacks (empty if none)
#   CPU_BYTESLICE_ORAM_HAS_VP2INTERSECT  -- ON/OFF
#   CPU_BYTESLICE_ORAM_FEATURE_PROBE_OK  -- OFF if the probe itself couldn't
#                                            be built/run (e.g. compiler too
#                                            old for __builtin_cpu_supports),
#                                            in which case the two lists above
#                                            are not meaningful and detection
#                                            is skipped.

set(_cpu_byteslice_oram_required_features
    avx2 avx512f avx512vl avx512bw avx512dq
    avx512vbmi avx512vbmi2 avx512cd aes vaes bmi bmi2 lzcnt)
set(_cpu_byteslice_oram_optional_features avx512vp2intersect)

set(_probe_src "${CMAKE_BINARY_DIR}/CMakeFiles/cpu_byteslice_oram_cpu_probe.cpp")
set(_probe_lines "#include <cstdio>\nint main() {\n  __builtin_cpu_init();\n")
foreach(_feat ${_cpu_byteslice_oram_required_features} ${_cpu_byteslice_oram_optional_features})
  string(APPEND _probe_lines
      "  std::printf(\"${_feat}:%d\\n\", __builtin_cpu_supports(\"${_feat}\") ? 1 : 0);\n")
endforeach()
string(APPEND _probe_lines "  return 0;\n}\n")
file(WRITE "${_probe_src}" "${_probe_lines}")

# A cross build cannot run the probe without an emulator: try_run would stop
# the configure and ask for cache entries that the unset() below erases.
# Skip the check there.  -march=native still targets the build host's CPU.
if(CMAKE_CROSSCOMPILING AND NOT CMAKE_CROSSCOMPILING_EMULATOR)
  message(WARNING
      "cpu_byteslice_oram: cross-compiling without an emulator, so the "
      "target's CPU features are not checked. -march=native selects the "
      "build host's CPU, not the target's.")
  set(CPU_BYTESLICE_ORAM_MISSING_BASELINE "")
  set(CPU_BYTESLICE_ORAM_HAS_VP2INTERSECT OFF)
  set(CPU_BYTESLICE_ORAM_FEATURE_PROBE_OK OFF)
  return()
endif()

# try_run caches its two result variables but NOT the run output.  If the
# cache were kept, every reconfigure after the first would skip the run, leave
# `_probe_output` empty, and the loop below would find no features at all --
# reporting VP2INTERSECT as missing on a machine that has it, while the
# compiled code, gated on __AVX512VP2INTERSECT__ under -march=native, uses it.
# The probe is a few microseconds; re-run it every time.
unset(_probe_run_result CACHE)
unset(_probe_compiled CACHE)
try_run(_probe_run_result _probe_compiled
    "${CMAKE_BINARY_DIR}/CMakeFiles"
    "${_probe_src}"
    RUN_OUTPUT_VARIABLE _probe_output)

set(CPU_BYTESLICE_ORAM_MISSING_BASELINE "")
set(CPU_BYTESLICE_ORAM_HAS_VP2INTERSECT OFF)
set(CPU_BYTESLICE_ORAM_FEATURE_PROBE_OK ${_probe_compiled})

if(NOT _probe_compiled OR NOT _probe_run_result EQUAL 0)
  message(WARNING
      "cpu_byteslice_oram: could not probe this machine's CPU features "
      "(__builtin_cpu_supports unavailable or the probe crashed) -- skipping "
      "the friendly pre-build check. -march=native will still be used; a "
      "missing required extension will now surface as a compiler error "
      "instead of a clear message.")
  set(CPU_BYTESLICE_ORAM_FEATURE_PROBE_OK OFF)
else()
  # A Windows console program writes "\r\n"; the anchored regex below would
  # then match no line at all, which would silently report every feature
  # missing (the required ones stay off the MISSING list too, so the only
  # visible symptom would be the VP2INTERSECT warning firing on a CPU that has
  # it).
  string(REPLACE "\r" "" _probe_output "${_probe_output}")
  string(REPLACE "\n" ";" _probe_lines_list "${_probe_output}")
  foreach(_line ${_probe_lines_list})
    if(_line MATCHES "^([a-z0-9-]+):([01])$")
      set(_feat "${CMAKE_MATCH_1}")
      set(_supported "${CMAKE_MATCH_2}")
      if(_feat STREQUAL "avx512vp2intersect")
        if(_supported STREQUAL "1")
          set(CPU_BYTESLICE_ORAM_HAS_VP2INTERSECT ON)
        endif()
      elseif(_supported STREQUAL "0")
        list(APPEND CPU_BYTESLICE_ORAM_MISSING_BASELINE "${_feat}")
      endif()
    endif()
  endforeach()
endif()
