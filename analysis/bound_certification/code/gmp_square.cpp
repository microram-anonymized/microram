// Optional accelerator for an exact nonnegative polynomial convolution.
// Compile: g++ -O3 -shared -fPIC gmp_square.cpp -lgmp -o libgmp_square.so
#include <gmp.h>
#include <cstring>
#include <cstddef>
extern "C" int square_le(const unsigned char *src, std::size_t n,
                          unsigned char *dst, std::size_t out_n) {
    if (out_n < 2*n) return 1;
    mpz_t x, y;
    mpz_inits(x, y, nullptr);
    mpz_import(x, n, -1, 1, 0, 0, src);
    mpz_mul(y, x, x);
    std::memset(dst, 0, out_n);
    std::size_t count=0;
    mpz_export(dst, &count, -1, 1, 0, 0, y);
    mpz_clears(x, y, nullptr);
    return count <= out_n ? 0 : 2;
}
