// Test-only oracle: prints upstream gl64_point() for a fixed list of (log_n, position).
// Build: g++ -std=c++17 -O2 -DBLK_FIELD=2 -DDIGEST_WORDS=8 -I UPSTREAM/blocks scripts/points_cpp_oracle.cpp
#include <cstdio>
#include "base.h"
#include "field/field.h"
#include "code/cosets.h"
int main() {
  const unsigned logs[] = {1, 5, 13, 17, 18, 23, 32, 33, 40};
  for (unsigned log_n : logs)
    for (unsigned long long i : {0ull, 1ull, 2ull, 3ull, 37ull, 1000003ull, (1ull << 32) + 5, (1ull << 39) - 1}) {
      if ((i >> log_n) != 0) continue;
      std::printf("%u %llu %llu\n", log_n, i, (unsigned long long)blk::gl64_point(log_n, i));
    }
}
