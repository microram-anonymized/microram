#pragma once

// Implementation detail of the public adapters' `access` / `Access`: decides,
// at compile time, which of the four callback shapes a user callback has --
// void(value), void(value, found), void(key, value), void(key, value, found)
// -- and invokes it with that shape.  A shape that takes the key may change
// it, so the adapters then erase the source key and write the destination
// (`changes_key`).  The dispatch depends only on the callback's type, never
// on secret data.

#include <functional>
#include <type_traits>
#include <utility>

namespace cpu_byteslice_oram {
namespace detail {

// Prefer the value/presence form over the two-argument key/value form:
// a pointer (or integer) value could otherwise convert implicitly to bool.
template <class Update, class KeyArg, class ValueArg>
struct AccessCallback {
  static constexpr bool key_value_found =
      std::is_invocable_v<Update&, KeyArg, ValueArg, bool>;
  static constexpr bool value_found =
      std::is_invocable_v<Update&, ValueArg, bool>;
  static constexpr bool key_value =
      std::is_invocable_v<Update&, KeyArg, ValueArg>;
  static constexpr bool changes_key =
      key_value_found || (!value_found && key_value);

  static void Invoke(Update& update, KeyArg key, ValueArg value, bool found) {
    if constexpr (key_value_found) {
      InvokeVoid(update, key, value, bool(found));
    } else if constexpr (value_found) {
      InvokeVoid(update, value, bool(found));
    } else if constexpr (key_value) {
      InvokeVoid(update, key, value);
    } else {
      static_assert(std::is_invocable_v<Update&, ValueArg>,
                    "Access callback must accept value[, found] or key, value[, found]");
      InvokeVoid(update, value);
    }
  }

 private:
  template <class... Args>
  static void InvokeVoid(Update& update, Args&&... args) {
    static_assert(std::is_void_v<std::invoke_result_t<Update&, Args...>>,
                  "Access callbacks must return void and mutate their arguments");
    std::invoke(update, std::forward<Args>(args)...);
  }
};

}  // namespace detail
}  // namespace cpu_byteslice_oram
