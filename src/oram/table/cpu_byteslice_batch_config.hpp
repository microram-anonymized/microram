#pragma once

// Public configuration types shared by the batched online access paths: the
// per-tile lane limit, the result layout, and the per-lane operation kind.
#include <cstddef>
#include <cstdint>

namespace microram {
namespace byteslice {

// Local masks and byte indices always describe one 64-lane SIMD tile.
inline constexpr size_t kMaxBatchLanes = 64;
inline constexpr unsigned kMaxOnlineParticipants = 8;  // caller included
inline constexpr size_t kMaxCombinedBatchLanes =
    kMaxBatchLanes * kMaxOnlineParticipants;

// How a chunk's probe results are laid out between the cascade and its
// consumers (table DESIGN.md, "Share extraction and dense scans across
// lanes").  Dense and
// pooled results are always accumulated SLICED (value line v, lane j at
// byte j); a hashed table's result is extracted per lane.  PUBLIC, fixed per
// instance; it changes instruction streams, never trace shape.
//   kRows              the reference: hashed results into per-lane rows, the
//                      dense accumulator merged into them by a scalar byte
//                      CMOV loop, and parallel tiles copying rows back into
//                      the sliced probe bank.
//   kSlicedPlaceAtLane sliced throughout: the hashed extract places each
//                      lane's byte at its own column with pair permutes, so
//                      no row exists and no transpose runs.
//
// kSlicedPlaceAtLane reaches the sliced result without any 64x64 transpose,
// which is strictly less work than converting rows wholesale in either
// direction, so no transposing layout is offered.
enum class BatchResultLayout : uint8_t {
  kRows,
  kSlicedPlaceAtLane
};

// What one lane asks for.  PUBLIC, exactly as which of Read / Write / Erase /
// Exchange a caller invokes is public; only the key, the values and the
// outcome are secret.
enum class BatchOp : uint8_t {
  kRead,
  // Skips the hierarchy lookup when neither the previous value nor presence
  // is requested. A write that returns the previous value or presence probes
  // first, like kReadThenWrite.
  kWrite,
  kErase,
  kExchange,
  // Explicitly probes before replacing the value, even without outputs.
  kReadThenWrite
};

}  // namespace byteslice
}  // namespace microram
