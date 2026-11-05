// Independent oracle using Anthropic's pinned C++ blocks/chain/chain.h.
// This is a component differential, NOT full verifier equivalence.
// Built only against the exact upstream C++ source in GitHub Actions.
#include <array>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <vector>
#include <cstdio>
#include <string>

#include "chain/chain.h"
#include "hash/hash.h"

static void print_digest(const char *name, const blk::Digest &d) {
  blk::u8 b[32];
  blk::digest_to_bytes(d, b);
  std::printf("%s=", name);
  for (int i=0; i<32; ++i) std::printf("%02x", (unsigned)b[i]);
  std::printf("\n");
}
static void print_ext(const char *name, const blk::E &e) {
  std::printf("%s=%llu,%llu,%llu\n", name,
              (unsigned long long)e.c[0].v,
              (unsigned long long)e.c[1].v,
              (unsigned long long)e.c[2].v);
}
static std::vector<blk::u8> read_bytes(const char *path) {
  std::ifstream input(path, std::ios::binary);
  if (!input) {
    std::fprintf(stderr, "cannot read %s\n", path);
    std::exit(2);
  }
  return std::vector<blk::u8>(std::istreambuf_iterator<char>(input),
                              std::istreambuf_iterator<char>());
}
int main(int argc, char **argv) {
  if (argc != 4) {
    std::fprintf(stderr, "usage: cpp-transcript-oracle POLICY LAYOUT SCALES\n");
    return 2;
  }
  blk::Hasher configuration(blk::Tag(blk::Domain::PARAMETERS), 2);
  configuration.push_u64(3);
  for (int i=1; i<=3; ++i) {
    const auto bytes = read_bytes(argv[i]);
    configuration.push_u64((blk::u64)bytes.size());
    configuration.push(bytes.data(), bytes.size());
  }
  print_digest("configuration", configuration.finish());
  std::array<blk::u8,32> param{}, salt{};
  for (unsigned i=0; i<32; ++i) {
    param[i] = (blk::u8)((7*i+3)%251);
    salt[i] = (blk::u8)((5*i+1)%251);
  }
  blk::FirstQuery q;
  q.label = 7;
  q.salted = true;
  q.salt_in_proof = true;
  blk::digest_from_bytes(param.data(), q.parameters);
  blk::digest_from_bytes(salt.data(), q.salt);
  const std::string statement = "rustflashprove-crosslang-v1";
  q.statement.assign(statement.begin(), statement.end());
  blk::Chain chain(q);
  print_digest("rho0", chain.value());
  const blk::u64 m1[] = {4, 5, 6, 7, 8, 9};
  chain.round(m1, blk::ChainKind::ALGEBRAIC);
  print_digest("rho1", chain.value());
  print_ext("e1", chain.draw_E());
  const blk::u64 m2[] = {1, 1, 1};
  chain.round(m2, blk::ChainKind::EMPTY);
  print_digest("rho2", chain.value());
  const blk::u64 m3[] = {11, 22, 33, 44};
  chain.round(m3, blk::ChainKind::POSITIONS);
  print_digest("rho3", chain.value());
  std::printf("p3=");
  for (unsigned i=0; i<5; ++i) {
    if (i) std::printf(",");
    std::printf("%llu", (unsigned long long)chain.draw_position(10));
  }
  std::printf("\n");
  print_ext("e3", chain.draw_E());
  chain.round(blk::ChainKind::SEED);
  print_digest("rho4", chain.value());
  print_ext("z4", chain.draw_E());
  print_ext("beta4", chain.draw_E_nonzero());
  return 0;
}
