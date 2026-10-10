#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <chrono>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <optional>
#include <queue>
#include <span>
#include <sys/mman.h>
#include <sys/resource.h>
#include <unistd.h>
#include <unordered_map>
#include <vector>

using namespace std;

using uintff = uint16_t; // Width for storing finite field elements
using uintffof =
    uint32_t; // Width for storing finite field operation results with overflow
using uintv = uint16_t;  // Width for storing graph vertices
using uintpow = uint8_t; // Width for storing variable powers
using uintml = uint16_t; // Width for storing monomial length
using uintpl = uint16_t; // Width for storing polynomial length
using uintcl = uint16_t; // Width for storing certificate length
constexpr size_t ff_bytes = 2;
constexpr size_t v_bytes = 2;
constexpr size_t pow_bytes = 1;
constexpr size_t mono_len_bytes = 2;
constexpr size_t poly_len_bytes = 2;
constexpr size_t cert_len_bytes = 2;
constexpr size_t rule_idx_bytes = 4;
constexpr size_t aut_idx_bytes = 4;

// ----- Finite field parameter -----

uintff ff_order = 4099;

uintff ff_add(uintff a, uintff b) {
  uintffof s = (uintffof)a + b;
  return s < ff_order ? s : s - ff_order;
}

uintff ff_mul(uintff a, uintff b) {
  uintffof p = (uintffof)a * b;
  return p < ff_order ? p : p % ff_order;
}

uintff ff_sub(uintff a, uintff b) {
  uintffof d = (uintffof)a + ff_order - b;
  return d < ff_order ? d : d - ff_order;
}

uintff ff_pow(uintff n, uintff p) {
  uintff res = 1;
  while (p > 0) {
    if (p & 1)
      res = ff_mul(res, n);
    n = ff_mul(n, n);
    p /= 2;
  }
  return res;
}

uintff ff_inverse(uintff n) {
  // Fermat's little theorem
  return ff_pow(n, ff_order - 2);
}

// ----- Partition mappings -----

struct WeakMapping;
struct WeakIterableCell;

struct WeakMapping {
  vector<int> u;
  vector<vector<int>> V;
  vector<int> cells;
  vector<int> cellIndices;
  int cellCount = 0;

  vector<WeakIterableCell> iterCells();
  vector<WeakIterableCell> iterCellsWithout(int excludedCell);
  WeakIterableCell iterable(int cell);
};

struct WeakIterableCell {
  const WeakMapping *mapping;
  int start;
  int end;
  int index;

  int sizeU();
  int sizeV();
  std::span<const int> iterU();
  std::span<const int> iterV();
};

vector<WeakIterableCell> WeakMapping::iterCells() {
  vector<WeakIterableCell> iterableCells;
  for (int i = 0; i < (int)cells.size(); i = cells[i])
    iterableCells.push_back(
        WeakIterableCell{this, i, cells[i], cellIndices[i]});
  return iterableCells;
}
vector<WeakIterableCell> WeakMapping::iterCellsWithout(int excludedCell) {
  vector<WeakIterableCell> iterableCells;
  for (int i = 0; i < (int)cells.size(); i = cells[i])
    if (i != excludedCell)
      iterableCells.push_back(
          WeakIterableCell{this, i, cells[i], cellIndices[i]});
  return iterableCells;
}
WeakIterableCell WeakMapping::iterable(int cell) {
  return WeakIterableCell{this, cell, cells[cell], cellIndices[cell]};
}

int WeakIterableCell::sizeU() { return end - start; }
int WeakIterableCell::sizeV() { return mapping->V[index].size(); }
std::span<const int> WeakIterableCell::iterU() {
  return std::span<const int>(mapping->u.data() + start, end - start);
}
std::span<const int> WeakIterableCell::iterV() {
  return std::span<const int>(mapping->V[index].data(),
                              mapping->V[index].size());
}

struct Bijection;
struct IterableCell;

struct Bijection {
  vector<int> u;
  vector<int> v;
  vector<int> cells;
  int cellCount = 0;

  explicit Bijection(int n) {
    u.resize(n);
    v.resize(n);
    cells.resize(n);
    cellCount = 1;

    iota(begin(u), end(u), 0);
    iota(begin(v), end(v), 0);
    cells[0] = n;
  }

  template <typename MappingType>
  vector<IterableCell> iterSplitCells(MappingType *nextMapping);
  template <typename MappingType>
  vector<IterableCell> iterSplitCellsWithout(MappingType *nextMapping,
                                             int excludedCell);
  vector<IterableCell> iterCells();
  vector<IterableCell> iterCellsWithout(int excludedCell);
  IterableCell iterable(int cell);
};

struct IterableCell {
  const Bijection *mapping;
  int start;
  int end;

  int size() { return end - start; }

  std::span<const int> iterU();
  std::span<const int> iterV();
  vector<IterableCell> iterCells(Bijection *nextMapping);
  vector<IterableCell> iterCellsWithout(Bijection *nextMapping,
                                        int excludedCell);
  vector<WeakIterableCell> iterCells(WeakMapping *nextMapping);
  vector<WeakIterableCell> iterCellsWithout(WeakMapping *nextMapping,
                                            int excludedCell);
  bool isSplitBy(Bijection *nextMapping);
  bool isSplitBy(WeakMapping *nextMapping);
};

template <typename MappingType>
vector<IterableCell> Bijection::iterSplitCells(MappingType *nextMapping) {
  vector<IterableCell> splitCells;
  for (auto &cell : this->iterCells())
    if (cell.isSplitBy(nextMapping))
      splitCells.push_back(cell);
  return splitCells;
}
template <typename MappingType>
vector<IterableCell> Bijection::iterSplitCellsWithout(MappingType *nextMapping,
                                                      int excludedCell) {
  vector<IterableCell> splitCells;
  for (int i = 0; i < cells.size(); i = cells[i])
    if (i != excludedCell && cells[i] != nextMapping->cells[i])
      splitCells.push_back(IterableCell{this, i, cells[i]});
  return splitCells;
}
vector<IterableCell> Bijection::iterCells() {
  vector<IterableCell> iterableCells;
  for (int i = 0; i < (int)cells.size(); i = cells[i])
    iterableCells.push_back(IterableCell{this, i, cells[i]});
  return iterableCells;
}
vector<IterableCell> Bijection::iterCellsWithout(int excludedCell) {
  vector<IterableCell> iterableCells;
  for (int i = 0; i < (int)cells.size(); i = cells[i])
    if (i != excludedCell)
      iterableCells.push_back(IterableCell{this, i, cells[i]});
  return iterableCells;
}
IterableCell Bijection::iterable(int cell) {
  return IterableCell{this, cell, cells[cell]};
}

std::span<const int> IterableCell::iterU() {
  return std::span<const int>(mapping->u.data() + start, end - start);
}
std::span<const int> IterableCell::iterV() {
  return std::span<const int>(mapping->v.data() + start, end - start);
}
vector<IterableCell> IterableCell::iterCells(Bijection *nextMapping) {
  vector<IterableCell> subcells;
  for (int i = start; i < end; i = nextMapping->cells[i])
    subcells.push_back(IterableCell{nextMapping, i, nextMapping->cells[i]});
  return subcells;
}
vector<IterableCell> IterableCell::iterCellsWithout(Bijection *nextMapping,
                                                    int excludedCell) {
  vector<IterableCell> subcells;
  for (int i = start; i < end; i = nextMapping->cells[i])
    if (i != excludedCell)
      subcells.push_back(IterableCell{nextMapping, i, nextMapping->cells[i]});
  return subcells;
}
vector<WeakIterableCell> IterableCell::iterCells(WeakMapping *nextMapping) {
  vector<WeakIterableCell> subcells;
  for (int i = start; i < end; i = nextMapping->cells[i])
    subcells.push_back(WeakIterableCell{nextMapping, i, nextMapping->cells[i],
                                        nextMapping->cellIndices[i]});
  return subcells;
}
vector<WeakIterableCell>
IterableCell::iterCellsWithout(WeakMapping *nextMapping, int excludedCell) {
  vector<WeakIterableCell> subcells;
  for (int i = start; i < end; i = nextMapping->cells[i])
    if (i != excludedCell)
      subcells.push_back(WeakIterableCell{nextMapping, i, nextMapping->cells[i],
                                          nextMapping->cellIndices[i]});
  return subcells;
}
bool IterableCell::isSplitBy(Bijection *nextMapping) {
  return end != nextMapping->cells[start];
}
bool IterableCell::isSplitBy(WeakMapping *nextMapping) {
  return end != nextMapping->cells[start] ||
         (int)nextMapping->V[nextMapping->cellIndices[start]].size() !=
             end - start;
}

// ----- Polynomial -----

struct Variable {
  uintv i, j;
};

struct VariablePower {
  uintpow pow;
  Variable var;
};

struct Monomial {
  uintff coeff;
  vector<VariablePower> vars;
};

using Polynomial = vector<Monomial>;

Polynomial withCoef(Polynomial p, uintff c) {
  p[0].coeff = c;
  return p;
}

Polynomial productFromIndices(Bijection &mapping,
                              const vector<int> &nonIndividualized,
                              uintff coeff) {
  // we know that the mapping is discrete at this point
  Monomial m{.coeff = coeff, .vars = {}};
  m.vars.reserve(nonIndividualized.size());
  for (int i : nonIndividualized)
    m.vars.push_back({1, {(uintv)mapping.u[i], (uintv)mapping.v[i]}});
  sort(begin(m.vars), end(m.vars), [](auto &x, auto &y) {
    return x.var.i < y.var.i || (x.var.i == y.var.i && x.var.j < y.var.j);
  });
  return {m};
}

Polynomial MPush(Polynomial m, uintv u, uintv v) {
  auto Xuv = VariablePower{1, {u, v}};
  m[0].vars.insert(upper_bound(begin(m[0].vars), end(m[0].vars), Xuv,
                               [](const auto &x, const auto &y) {
                                 return x.var.i < y.var.i ||
                                        (x.var.i == y.var.i &&
                                         x.var.j < y.var.j);
                               }),
                   Xuv);
  return m;
}

// ----- Proof generation -----

struct Proof;

struct ProofContext {

  enum TableName : uint8_t {
    Indicator,
    Mapping,
    MappingInv,
    NewMapping,
    NewMappingInv,
    D,
    Xuv
  };

  Proof *proof;
  Polynomial M = {};
  uint32_t lookupM = 0;

  array<unordered_map<int, uint32_t>, 7> tables = {};
  vector<unordered_map<int, uint32_t>> tableXuv = {};

  uint32_t lookup(TableName name, int u) {
    assert(name != Xuv);
    assert(tables[(size_t)name].find(u) != end(tables[(size_t)name]));
    return tables[(size_t)name][u];
  }
  uint32_t lookup(TableName name, int u, int v) {
    assert(name == Xuv);
    assert(tableXuv[u].find(v) != end(tableXuv[u]));
    return tableXuv[u][v];
  }

  uint32_t write(TableName name, vector<Polynomial> &cert,
                 vector<uint32_t> &base, int u);
  uint32_t write(TableName, vector<Polynomial> &cert, vector<uint32_t> &base,
                 int u, int v);
  uint32_t writeM(vector<Polynomial> &cert, vector<uint32_t> &base);

  void flushMappings() {
    for (auto &[u, idx] : tables[NewMapping])
      tables[Mapping][u] = idx;
    tables[NewMapping].clear();

    for (auto &[v, idx] : tables[NewMappingInv])
      tables[MappingInv][v] = idx;
    tables[NewMappingInv].clear();
  }
};

enum RuleType : uint8_t {
  IDEAL,
  SUBSTITUTION,
  ROWNZ,
  COLNZ,
  ROWS,
  COLS,
  ISO,
  EXISO,
  BIN
};

struct TautologyTable {
  array<optional<uint32_t>, 9> tables0;
  array<unordered_map<int, uint32_t>, 9> tables1;
  array<vector<unordered_map<int, uint32_t>>, 9> tables2;
  array<vector<vector<unordered_map<int, uint32_t>>>, 9> tables3;
};

static_assert(std::endian::native == std::endian::little,
              "proof files are little-endian");

struct MemoryPool {

  void allocAnonymous(uint64_t bytes) {
    if (data) {
      // No need to msync for anonymous mappings
      munmap(data, allocatedBytes);
      data = nullptr;
    }
    if (fd != -1) {
      close(fd);
      fd = -1;
      filepath.clear();
    }

    void *p = mmap(nullptr, (size_t)bytes, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (p == MAP_FAILED) {
      cerr << "Failed to allocate anonymous memory for memory pool" << endl;
      exit(1);
    }

    fd = -1;
    filepath.clear();
    data = (uint8_t *)p;
    allocatedBytes = bytes;
    size = 0;
  }

  void allocAt(const std::string &path, uint64_t bytes) {
    if (data) {
      msync(data, allocatedBytes, MS_SYNC);
      munmap(data, allocatedBytes);
      data = nullptr;
    }
    if (fd != -1) {
      close(fd);
      fd = -1;
      filepath.clear();
    }

    int tfd = ::open(path.c_str(), O_CREAT | O_TRUNC | O_RDWR, 0644);
    if (tfd == -1) {
      cerr << "Failed to open output file for memory pool: " << path << endl;
      exit(1);
    }
    if (ftruncate(tfd, (off_t)bytes) == -1) {
      cerr << "Failed to resize output file for memory pool (insufficient "
              "space?): "
           << path << endl;
      close(tfd);
      exit(1);
    }

    void *p = mmap(nullptr, (size_t)bytes, PROT_READ | PROT_WRITE, MAP_SHARED,
                   tfd, 0);
    if (p == MAP_FAILED) {
      cerr << "Failed to mmap output file for memory pool: " << path << endl;
      close(tfd);
      exit(1);
    }

    fd = tfd;
    filepath = path;
    data = (uint8_t *)p;
    allocatedBytes = bytes;
    size = 0;
  }

  void write(char *writeData, int writeSize) {
    if (size + writeSize > allocatedBytes) {
      cerr << "Memory pool overflow during write operation." << endl;
      exit(1);
    }
    memcpy(data + size, writeData, writeSize);
    size += writeSize;
  }

  void write(char *writeData, int writeSize, uint64_t writeOffset) {
    memcpy(data + writeOffset, writeData, writeSize);
  }

  void read(char *readBuffer, int readSize, uint64_t readOffset) {
    memcpy(readBuffer, data + readOffset, readSize);
  }

  void commitToFile(const std::string &path, uint64_t bytesToWrite) {
    int tfd = ::open(path.c_str(), O_CREAT | O_TRUNC | O_WRONLY, 0644);
    if (tfd == -1) {
      cerr << "Failed to open output file for commit: " << path << endl;
      exit(1);
    }
    uint64_t written = 0;
    while (written < bytesToWrite) {
      ssize_t w =
          ::write(tfd, data + written,
                  (size_t)min<uint64_t>(bytesToWrite - written, 1ull << 30));
      if (w <= 0) {
        cerr << "Failed to write proof to output file during commit" << endl;
        close(tfd);
        exit(1);
      }
      written += (uint64_t)w;
    }
    fsync(tfd);
    close(tfd);
  }

  ~MemoryPool() {
    if (data) {
      if (fd != -1)
        msync(data, allocatedBytes, MS_SYNC);
      munmap(data, allocatedBytes);
      data = nullptr;
    }
    if (fd != -1) {
      close(fd);
      fd = -1;
    }
  }

  uint64_t allocatedBytes = 0;
  uint64_t size = 0;
  uint8_t *data = nullptr;
  int fd = -1;
  std::string filepath;
};

struct Proof {
  explicit Proof(int n, string proofFile, uint64_t memoryLimit, bool inMemory) {
    if (inMemory)
      inmemProof.allocAnonymous(memoryLimit);
    else
      inmemProof.allocAt(proofFile, memoryLimit);

    tautologies.tables2[ISO].resize(n);
    tautologies.tables2[BIN].resize(n);

    tautologies.tables3[ROWNZ].resize(n,
                                      vector<unordered_map<int, uint32_t>>(n));
    tautologies.tables3[COLNZ].resize(n,
                                      vector<unordered_map<int, uint32_t>>(n));
  }
  TautologyTable tautologies;
  // For writing canon ex iso
  uint32_t lookupTautology(RuleType name) {
    if (!tautologies.tables0[name].has_value())
      tautologies.tables0[name] = writeTautology(name);

    return tautologies.tables0[name].value();
  }
  uint32_t lookupTautology(RuleType name, int u) {
    auto it = tautologies.tables1[name].find(u);
    if (it != tautologies.tables1[name].end())
      return it->second;

    return tautologies.tables1[name][u] = writeTautology(name, u);
  }
  uint32_t lookupTautology(RuleType name, int u, int v) {
    auto it = tautologies.tables2[name][u].find(v);
    if (it != tautologies.tables2[name][u].end())
      return it->second;

    return tautologies.tables2[name][u][v] = writeTautology(name, u, v);
  }
  uint32_t lookupTautology(RuleType name, int u, int v, int w) {
    auto it = tautologies.tables3[name][u][v].find(w);
    if (it != tautologies.tables3[name][u][v].end())
      return it->second;

    return tautologies.tables3[name][u][v][w] = writeTautology(name, u, v, w);
  }

  vector<ProofContext> context;
  ProofContext &currContext() { return rbegin(context)[0]; }
  ProofContext &prevContext() { return rbegin(context)[1]; }
  void popContext() { context.pop_back(); }
  void pushContext(int graphSize) { // called before initializing the search,
                                    // while the context stack is empty
    context.push_back(ProofContext{.proof = this});
    context.back().M = {{1, {}}};
    context.back().tableXuv.resize(graphSize);
    // Pre-reserve for Mapping and MappingInv which will be filled for all
    // vertices
    currContext().tables[ProofContext::Mapping].reserve(graphSize);
    currContext().tables[ProofContext::MappingInv].reserve(graphSize);
    for (int u = 0; u < graphSize; u++) {
      currContext().tables[ProofContext::Mapping][u] =
          lookupTautology(RuleType::ROWS, u);
      currContext().tables[ProofContext::MappingInv][u] =
          lookupTautology(RuleType::COLS, u);
    }
  }
  void pushContext(int u, int v, int graphSize) {
    context.push_back(ProofContext{.proof = this});
    context.back().M = MPush(rbegin(context)[1].M, u, v);
    context.back().tableXuv.resize(graphSize);
    vector<Polynomial> Xuv = {
        {Monomial{1, {VariablePower{1, Variable{(uintv)u, (uintv)v}}}}}};
  }

  void write(char *data, uint32_t bytes) {
    // Redirect write into the mapped pool
    inmemProof.write(data, (int)bytes);
  }

  MemoryPool inmemProof;
  vector<uint64_t> ruleOffset;
  vector<uint32_t> ruleLength;

  uint32_t ruleCount = 0;
  uint32_t writeTautology(RuleType rule) {
    assert(rule == EXISO);
    if (!~ruleCount) {
      cerr << "Rule count overflow." << endl;
      exit(1);
    }
    ruleOffset.push_back(inmemProof.size);

    inmemProof.write((char *)&rule, 1);

    uint32_t zero = 0; // index of identity automorphism
    inmemProof.write((char *)&zero, aut_idx_bytes);

    ruleLength.push_back(inmemProof.size - ruleOffset.back());
    return ruleCount++;
  }
  uint32_t writeTautology(RuleType rule, uintv u) {
    assert(rule == ROWS || rule == COLS);
    if (!~ruleCount) {
      cerr << "Rule count overflow." << endl;
      exit(1);
    }
    ruleOffset.push_back(inmemProof.size);
    inmemProof.write((char *)&rule, 1);
    inmemProof.write((char *)&u, v_bytes);
    ruleLength.push_back(inmemProof.size - ruleOffset.back());
    return ruleCount++;
  }
  uint32_t writeTautology(RuleType rule, uintv u, uintv v) {
    assert(rule == ISO || rule == BIN);
    if (!~ruleCount) {
      cerr << "Rule count overflow." << endl;
      exit(1);
    }
    ruleOffset.push_back(inmemProof.size);
    inmemProof.write((char *)&rule, 1);
    inmemProof.write((char *)&u, v_bytes);
    inmemProof.write((char *)&v, v_bytes);
    ruleLength.push_back(inmemProof.size - ruleOffset.back());
    return ruleCount++;
  }
  uint32_t writeTautology(RuleType rule, uintv u, uintv v, uintv w) {
    assert(rule == ROWNZ || rule == COLNZ);
    if (!~ruleCount) {
      cerr << "Rule count overflow." << endl;
      exit(1);
    }
    ruleOffset.push_back(inmemProof.size);
    inmemProof.write((char *)&rule, 1);
    inmemProof.write((char *)&u, v_bytes);
    inmemProof.write((char *)&v, v_bytes);
    inmemProof.write((char *)&w, v_bytes);
    ruleLength.push_back(inmemProof.size - ruleOffset.back());
    return ruleCount++;
  }
  uint32_t writeIdeal(vector<Polynomial> &cert, vector<uint32_t> &base) {
    if (!~ruleCount) {
      cerr << "Rule count overflow." << endl;
      exit(1);
    }
    ruleOffset.push_back(inmemProof.size);

    RuleType rule = IDEAL;
    inmemProof.write((char *)&rule, 1);
    uintcl certSize = cert.size();
    inmemProof.write((char *)&certSize, cert_len_bytes);
    for (auto &b : base)
      inmemProof.write((char *)&b, rule_idx_bytes);

    for (auto &poly : cert) {
      uintpl polySize = poly.size();
      inmemProof.write((char *)&polySize, poly_len_bytes);

      for (auto &mono : poly) {
        uintml monoSize = mono.vars.size();
        inmemProof.write((char *)&monoSize, mono_len_bytes);

        for (auto &var : mono.vars) {
          uint32_t compressedVar = ((uint32_t)var.var.i << 20) |
                                   ((uint32_t)var.var.j << 8) | var.pow;
          inmemProof.write((char *)&compressedVar, 4);
        }

        inmemProof.write((char *)&mono.coeff, ff_bytes);
      }
    }

    ruleLength.push_back(inmemProof.size - ruleOffset.back());
    return ruleCount++;
  }
  uint32_t writeSubstitution(uint32_t fact, uint32_t aut) {
    if (!~ruleCount) {
      cerr << "Rule count overflow." << endl;
      exit(1);
    }
    ruleOffset.push_back(inmemProof.size);
    RuleType rule = SUBSTITUTION;
    inmemProof.write((char *)&rule, 1);
    inmemProof.write((char *)&fact, rule_idx_bytes);
    inmemProof.write((char *)&aut, aut_idx_bytes);
    ruleLength.push_back(inmemProof.size - ruleOffset.back());
    return ruleCount++;
  }

  void compressAndCommit() {
    vector<bool> used(ruleCount);
    used.back() = true;
    vector<uint32_t> stack = {ruleCount - 1};
    while (!stack.empty()) {
      uint64_t offset = ruleOffset[stack.back()];
      stack.pop_back();
      RuleType tag = (RuleType)inmemProof.data[offset];
      if (tag == RuleType::SUBSTITUTION) {
        uint32_t link;
        inmemProof.read((char *)&link, rule_idx_bytes, offset + 1);
        if (!used[link]) {
          used[link] = true;
          stack.push_back(link);
        }
      } else if (tag == RuleType::IDEAL) {
        uintcl certSize;
        inmemProof.read((char *)&certSize, cert_len_bytes, offset + 1);
        uint64_t linkOffset = offset + 1 + cert_len_bytes;
        for (uint32_t i = 0; i < certSize; i++) {
          uint32_t link;
          inmemProof.read((char *)&link, rule_idx_bytes, linkOffset);
          if (!used[link]) {
            used[link] = true;
            stack.push_back(link);
          }
          linkOffset += rule_idx_bytes;
        }
      }
    }

    uint32_t oldRuleCount = ruleCount;
    ruleCount = 0;
    vector<uint32_t> newIdx(oldRuleCount);

    // Patch links in place
    for (uint32_t i = 0; i < oldRuleCount; i++)
      if (used[i]) {
        newIdx[i] = ruleCount++;
      }

    for (uint32_t i = 0; i < oldRuleCount; i++)
      if (used[i]) {
        uint64_t offset = ruleOffset[i];
        RuleType tag = (RuleType)inmemProof.data[offset];
        if (tag == RuleType::IDEAL) {
          uintcl certSize;
          inmemProof.read((char *)&certSize, cert_len_bytes, offset + 1);
          uint64_t linkOffset = offset + 1 + cert_len_bytes;
          for (uint32_t j = 0; j < certSize; j++) {
            uint32_t link;
            inmemProof.read((char *)&link, rule_idx_bytes, linkOffset);
            link = newIdx[link];
            inmemProof.write((char *)&link, rule_idx_bytes, linkOffset);
            linkOffset += rule_idx_bytes;
          }
        } else if (tag == RuleType::SUBSTITUTION) {
          uint32_t link;
          inmemProof.read((char *)&link, rule_idx_bytes, offset + 1);
          link = newIdx[link];
          inmemProof.write((char *)&link, rule_idx_bytes, offset + 1);
        }
      }

    // In-place compaction via memmove starting at the first rule offset
    uint64_t dst = ruleOffset.empty() ? inmemProof.size : ruleOffset[0];
    for (uint32_t i = 0; i < oldRuleCount; i++)
      if (used[i]) {
        uint64_t src = ruleOffset[i];
        uint32_t len = ruleLength[i];
        memmove(inmemProof.data + dst, inmemProof.data + src, len);
        dst += len;
      }

    // Truncate the mapped file
    inmemProof.size = dst;
    if (inmemProof.fd != -1) {
      ftruncate(inmemProof.fd, (off_t)dst);
      msync(inmemProof.data, dst, MS_SYNC);
    }
  }
};
uint32_t ProofContext::write(TableName name, vector<Polynomial> &cert,
                             vector<uint32_t> &base, int u) {
  assert(name != Xuv);
  return tables[(size_t)name][u] = proof->writeIdeal(cert, base);
}

uint32_t ProofContext::write(TableName name, vector<Polynomial> &cert,
                             vector<uint32_t> &base, int u, int v) {
  assert(name == Xuv);
  return tableXuv[u][v] = proof->writeIdeal(cert, base);
}

uint32_t ProofContext::writeM(vector<Polynomial> &cert,
                              vector<uint32_t> &base) {
  return lookupM = proof->writeIdeal(cert, base);
}

template <typename MappingType>
void proveSplit(Bijection &prevMapping, MappingType &mapping, vector<int> &uDeg,
                vector<int> &vDeg, vector<vector<uintv>> &graph, int W,
                Proof &proof) {
  int WEnd = prevMapping.cells[W];
  int WSize = WEnd - W;

  vector<bool> WSet(graph.size());
  for (auto &u : prevMapping.iterable(W).iterU())
    WSet[u] = true;

  // Prebuild reusable buffers
  vector<Polynomial> indicatorCert(WSize, {Monomial{1, {}}});
  vector<uint32_t> indicatorBase;
  indicatorBase.reserve(WSize);

  vector<Polynomial> isoSumCert(WSize, {Monomial{1, {}}});
  vector<uint32_t> isoSumBase;
  isoSumBase.reserve(WSize);

  vector<Polynomial> dCert;
  vector<uint32_t> dBase;

  vector<Polynomial> degSumCert;
  vector<uint32_t> degSumBase;

  vector<Polynomial> xuvCert(2);
  vector<uint32_t> xuvBase(2);

  vector<Polynomial> nmCert;
  vector<uint32_t> nmBase;

  vector<Polynomial> nmInvCert;
  vector<uint32_t> nmInvBase;

  // For each vertex u not in W
  // Prove ind_{u, W} M_nu
  for (auto &cell : prevMapping.iterCellsWithout(W))
    for (auto &u : cell.iterU()) {
      indicatorBase.clear();
      for (auto &v : prevMapping.iterable(W).iterV())
        indicatorBase.push_back(
            proof.currContext().lookup(ProofContext::Xuv, u, v));

      proof.currContext().write(ProofContext::Indicator, indicatorCert,
                                indicatorBase, u);
      // This should store the indicator in a lookup table as well
      // A proof context contains lookup tables to polynomials derived with
      // prefix M_nu!!!
    }

  // For each vertex u (of a cell that has been split)
  // Prove d_{u, W} M_nu
  for (auto &cell : prevMapping.iterSplitCells(&mapping))
    for (auto &u : cell.iterU()) {
      // Prove Iso[u, W] sum
      // We do this separately for efficiency reasons
      isoSumBase.clear();
      for (auto &v : prevMapping.iterable(W).iterV())
        isoSumBase.push_back(proof.lookupTautology(RuleType::ISO, u, v));

      uint32_t isoSumIdx = proof.writeIdeal(isoSumCert, isoSumBase);

      // Prove d_{u, W}
      dCert.clear();
      dBase.clear();

      dCert.push_back(proof.currContext().M);
      dBase.push_back(isoSumIdx);

      for (int j = 0; j < (int)graph[u].size(); j++) {
        int u2 = graph[u][j];
        dCert.push_back({Monomial{(uintff)(ff_order - 1), {}}});
        if (WSet[u2])
          dBase.push_back(
              proof.currContext().lookup(ProofContext::Mapping, u2));
        else
          dBase.push_back(
              proof.currContext().lookup(ProofContext::Indicator, u2));
      }

      for (auto &cell2 : prevMapping.iterCellsWithout(cell.start))
        for (auto &v : cell2.iterV()) {
          if (vDeg[v] > 0) {
            dCert.push_back({Monomial{(uintff)vDeg[v], {}}});
            dBase.push_back(
                proof.currContext().lookup(ProofContext::Xuv, u, v));
          }
        }

      proof.currContext().write(ProofContext::D, dCert, dBase, u);
    }

  // For each vertex u (of a cell that has been split)
  // For each vertex v in nu[u] such that vDeg != uDeg
  // Prove Xuv
  for (auto &cell : prevMapping.iterSplitCells(&mapping))
    for (auto &u : cell.iterU()) {
      for (auto &v : cell.iterV()) {
        if (uDeg[u] == vDeg[v])
          continue;

        degSumCert.clear();
        degSumBase.clear();

        // First prove deg(u, nu(W)) (xuv^2-xuv) + sum deg(v', nu(W)) xuv'xuv
        for (auto &v2 : cell.iterV()) {
          if (vDeg[v2] > 0) {
            degSumCert.push_back({Monomial{(uintff)vDeg[v2], {}}});
            if (v != v2)
              degSumBase.push_back(proof.lookupTautology(
                  RuleType::ROWNZ, u, min(v, v2), max(v, v2)));
            else
              degSumBase.push_back(proof.lookupTautology(RuleType::BIN, u, v));
          }
        }
        uint32_t degSumIdx = proof.writeIdeal(degSumCert, degSumBase);

        uintff coef = ff_inverse(ff_sub(uDeg[u], vDeg[v]));

        xuvCert[0] = {Monomial{coef, {{1, {(uintv)u, (uintv)v}}}}};
        xuvBase[0] = proof.currContext().lookup(ProofContext::D, u);

        xuvCert[1] = {withCoef(proof.currContext().M, coef)};
        xuvBase[1] = degSumIdx;

        proof.currContext().write(ProofContext::Xuv, xuvCert, xuvBase, u, v);
      }
    }

  // For each vertex u (of a cell that has been split)
  // Prove ind_{u, U'} - 1
  for (auto &cell : prevMapping.iterSplitCells(&mapping)) {
    for (auto &ucell : cell.iterCells(&mapping))
      for (auto &u : ucell.iterU()) {
        nmCert.clear();
        nmBase.clear();

        nmCert.push_back({Monomial{1, {}}});
        nmBase.push_back(proof.currContext().lookup(ProofContext::Mapping, u));

        for (auto &v : cell.iterV())
          if (uDeg[u] != vDeg[v]) {
            nmCert.push_back({Monomial{(uintff)(ff_order - 1), {}}});
            nmBase.push_back(
                proof.currContext().lookup(ProofContext::Xuv, u, v));
          }

        proof.currContext().write(ProofContext::NewMapping, nmCert, nmBase, u);
      }
  }

  // For each vertex v (of a cell that has been split)
  // Prove ind_{v, V'} - 1
  for (auto &cell : prevMapping.iterSplitCells(&mapping)) {
    for (auto &vcell : cell.iterCells(&mapping))
      for (auto &v : vcell.iterV()) {
        nmInvCert.clear();
        nmInvBase.clear();

        nmInvCert.push_back({Monomial{1, {}}});
        nmInvBase.push_back(
            proof.currContext().lookup(ProofContext::MappingInv, v));

        for (auto &u : cell.iterU())
          if (uDeg[u] != vDeg[v]) {
            nmInvCert.push_back({Monomial{(uintff)(ff_order - 1), {}}});
            nmInvBase.push_back(
                proof.currContext().lookup(ProofContext::Xuv, u, v));
          }

        proof.currContext().write(ProofContext::NewMappingInv, nmInvCert,
                                  nmInvBase, v);
      }
  }

  // Remove temporary split-level lookup tables and
  // replace current Mappings with NewMappings
  proof.currContext().flushMappings();
}

void proveWeak(WeakMapping &mapping, Proof &proof) {
  // Find a cell of mapping such that size(U) != size(mapping(U))
  // For optimization purposes, find the one with minimal size(U) *
  // size(mapping(U))
  int64_t prod = -1ll;
  WeakIterableCell cell{};
  for (auto &icell : mapping.iterCells()) {
    int64_t iprod = (int64_t)icell.sizeU() * icell.sizeV();
    if (icell.sizeU() != icell.sizeV() && (prod == -1ll || prod > iprod)) {
      prod = iprod;
      cell = icell;
    }
  }

  assert(prod >= 0);

  vector<Polynomial> cert(cell.sizeU() + cell.sizeV());
  vector<uint32_t> base(cell.sizeU() + cell.sizeV());

  uintff coef = ff_inverse(ff_sub(cell.sizeU(), cell.sizeV()));

  int i = 0;
  for (auto &v : cell.iterV()) {
    cert[i] = {Monomial{coef, {}}};
    base[i] = proof.currContext().lookup(ProofContext::MappingInv, v);
    i++;
  }

  for (auto &u : cell.iterU()) {
    cert[i] = {Monomial{(uintff)(ff_order - coef), {}}};
    base[i] = proof.currContext().lookup(ProofContext::Mapping, u);
    i++;
  }

  proof.currContext().writeM(cert, base);
}

WeakMapping splitWeak(Bijection &mapping, vector<int> &uDeg,
                      vector<int> &vDeg) {
  WeakMapping nextMapping;
  nextMapping.u = mapping.u;
  nextMapping.cells = mapping.cells;
  nextMapping.cellIndices.resize(mapping.u.size());
  nextMapping.cellCount = 0;

  for (int i = 0; i < (int)mapping.u.size(); i = mapping.cells[i]) {
    nextMapping.V.emplace_back();
    nextMapping.cellIndices[i] = nextMapping.cellCount;

    // set V pointer to the first vertex with grater degree than u[i]
    int vptr = i;
    while (vptr < mapping.cells[i] &&
           vDeg[mapping.v[vptr]] <= uDeg[mapping.u[i]]) {
      if (vDeg[mapping.v[vptr]] == uDeg[mapping.u[i]])
        nextMapping.V.back().push_back(mapping.v[vptr]);
      vptr++;
    }

    int prev = i;
    for (int j = i + 1; j < mapping.cells[i]; j++) {
      if (uDeg[mapping.u[j]] != uDeg[mapping.u[j - 1]]) {
        nextMapping.cells[j] = nextMapping.cells[prev];
        nextMapping.cells[prev] = j;
        prev = j;

        nextMapping.V.emplace_back();
        nextMapping.cellIndices[j] = ++nextMapping.cellCount;

        while (vptr < mapping.cells[i] &&
               vDeg[mapping.v[vptr]] <= uDeg[mapping.u[j]]) {
          if (vDeg[mapping.v[vptr]] == uDeg[mapping.u[j]])
            nextMapping.V.back().push_back(mapping.v[vptr]);
          vptr++;
        }
      }
    }

    nextMapping.cellCount++;
  }

  return nextMapping;
}

optional<WeakMapping> split(Bijection &mapping, vector<int> &uDeg,
                            vector<int> &vDeg, queue<int> &active_cells) {
  for (int i = 0; i < (int)mapping.u.size(); i = mapping.cells[i]) {
    sort(begin(mapping.u) + i, begin(mapping.u) + mapping.cells[i],
         [&](int a, int b) {
           return uDeg[a] < uDeg[b] || (uDeg[a] == uDeg[b] && a < b);
         });
    sort(begin(mapping.v) + i, begin(mapping.v) + mapping.cells[i],
         [&](int a, int b) {
           return vDeg[a] < vDeg[b] || (vDeg[a] == vDeg[b] && a < b);
         });
  }

  for (int i = 0; i < (int)mapping.u.size(); i++)
    if (uDeg[mapping.u[i]] != vDeg[mapping.v[i]])
      return splitWeak(mapping, uDeg, vDeg);

  for (int i = 0; i < (int)mapping.u.size(); i = mapping.cells[i]) {
    int prev = i;
    for (int j = i + 1; j < mapping.cells[i]; j++)
      if (uDeg[mapping.u[j]] != uDeg[mapping.u[j - 1]]) {
        mapping.cellCount++;
        mapping.cells[j] = mapping.cells[prev];
        mapping.cells[prev] = j;
        prev = j;

        active_cells.push(j);
      }
  }
  return {};
}

// The fact order is
// 1. u -> v for any two vertices u from U and v from V such that nu(U) != V
// 2. u -> V for any vertex u from U such that nu(U) = V
// 3. U -> v for any vertex v from V such that nu(U) = V
bool refineProve(Bijection &mapping, vector<vector<uintv>> &graph,
                 int first_active_cell, Proof &proof) {
  queue<int> active_cells;
  active_cells.push(first_active_cell);
  while (!active_cells.empty() && mapping.cellCount < (int)graph.size()) {
    int W = active_cells.front();
    active_cells.pop();

    // Save mapping for proof generation
    Bijection prevMapping = mapping;

    vector<int> uDeg(graph.size()), vDeg(graph.size());
    for (int i = W; i < mapping.cells[W]; i++) {
      for (int un : graph[mapping.u[i]])
        uDeg[un]++;
      for (int vn : graph[mapping.v[i]])
        vDeg[vn]++;
    }

    optional<WeakMapping> weakMapping;
    if ((weakMapping = split(mapping, uDeg, vDeg, active_cells))) {
      proveSplit(mapping, weakMapping.value(), uDeg, vDeg, graph, W, proof);
      proveWeak(weakMapping.value(), proof);
      return true;
    }

    if (mapping.cells != prevMapping.cells)
      proveSplit(prevMapping, mapping, uDeg, vDeg, graph, W, proof);
  }
  return false;
}

Bijection individualizeProve(Bijection mapping, int u, int v, Proof &proof) {
  int i = distance(begin(mapping.u), find(begin(mapping.u), end(mapping.u), u));
  int j = distance(begin(mapping.v), find(begin(mapping.v), end(mapping.v), v));

  int cell = 0;
  while (mapping.cells[cell] <= i)
    cell = mapping.cells[cell];

  while (i > cell) {
    swap(mapping.u[i], mapping.u[i - 1]);
    i--;
  }
  while (j > cell) {
    swap(mapping.v[j], mapping.v[j - 1]);
    j--;
  }

  // Prove Xuv for u in U and v in V where U != V
  for (auto &ucell : mapping.iterCells())
    for (auto &vcell : mapping.iterCellsWithout(ucell.start))
      for (auto &ut : ucell.iterU())
        for (auto &vt : vcell.iterV()) {
          vector<Polynomial> cert(1);
          vector<uint32_t> base(1);

          cert[0] = {Monomial{1, {{1, {(uintv)u, (uintv)v}}}}};
          base[0] = proof.prevContext().lookup(ProofContext::Xuv, ut, vt);

          proof.currContext().write(ProofContext::Xuv, cert, base, ut, vt);
        }

  // Prove mapping for u -> V where V != individualized cell
  for (auto &ucell : mapping.iterCellsWithout(cell))
    for (auto &ut : ucell.iterU()) {
      vector<Polynomial> cert(1);
      vector<uint32_t> base(1);

      cert[0] = {Monomial{1, {{1, {(uintv)u, (uintv)v}}}}};
      base[0] = proof.prevContext().lookup(ProofContext::Mapping, ut);

      proof.currContext().write(ProofContext::Mapping, cert, base, ut);
    }

  // Prove mapping for U -> v where U != individualized cell
  for (auto &vcell : mapping.iterCellsWithout(cell))
    for (auto &vt : vcell.iterV()) {
      vector<Polynomial> cert(1);
      vector<uint32_t> base(1);

      cert[0] = {Monomial{1, {{1, {(uintv)u, (uintv)v}}}}};
      base[0] = proof.prevContext().lookup(ProofContext::MappingInv, vt);

      proof.currContext().write(ProofContext::MappingInv, cert, base, vt);
    }

  mapping.cells[cell + 1] = mapping.cells[cell];
  mapping.cells[cell] = cell + 1;

  // Prove Xuv for u and V
  for (int i1 = cell + 1; i1 < mapping.cells[cell + 1]; i1++) {
    int vt = mapping.v[i1];

    vector<Polynomial> cert(1);
    vector<uint32_t> base(1);

    cert[0] = {proof.prevContext().M};
    base[0] = proof.lookupTautology(RuleType::ROWNZ, u, min(v, vt), max(v, vt));

    proof.currContext().write(ProofContext::Xuv, cert, base, u, vt);
  }

  // Prove Xuv for v and U
  for (int i1 = cell + 1; i1 < mapping.cells[cell + 1]; i1++) {
    int ut = mapping.u[i1];

    vector<Polynomial> cert(1);
    vector<uint32_t> base(1);

    cert[0] = {proof.prevContext().M};
    base[0] = proof.lookupTautology(RuleType::COLNZ, min(u, ut), max(u, ut), v);

    proof.currContext().write(ProofContext::Xuv, cert, base, ut, v);
  }

  // Prove mapping for u -> v
  vector<Polynomial> cert(1);
  vector<uint32_t> base(1);

  cert[0] = {proof.prevContext().M};
  base[0] = proof.lookupTautology(RuleType::BIN, u, v);

  proof.currContext().write(ProofContext::Mapping, cert, base, u);
  proof.currContext().write(ProofContext::MappingInv, cert, base, v);

  // Prove mapping for u -> V
  for (int i1 = cell + 1; i1 < mapping.cells[cell + 1]; i1++) {
    int ut = mapping.u[i1];

    vector<Polynomial> cert(2);
    vector<uint32_t> base(2);

    cert[0] = {Monomial{(uintff)(ff_order - 1), {}}};
    base[0] = proof.currContext().lookup(ProofContext::Xuv, ut, v);

    cert[1] = {Monomial{1, {{1, {(uintv)u, (uintv)v}}}}};
    base[1] = proof.prevContext().lookup(ProofContext::Mapping, ut);

    proof.currContext().write(ProofContext::Mapping, cert, base, ut);
  }

  // Prove mapping for U -> v
  for (int i1 = cell + 1; i1 < mapping.cells[cell + 1]; i1++) {
    int vt = mapping.v[i1];

    vector<Polynomial> cert(2);
    vector<uint32_t> base(2);

    cert[0] = {Monomial{(uintff)(ff_order - 1), {}}};
    base[0] = proof.currContext().lookup(ProofContext::Xuv, u, vt);

    cert[1] = {Monomial{1, {{1, {(uintv)u, (uintv)v}}}}};
    base[1] = proof.prevContext().lookup(ProofContext::MappingInv, vt);

    proof.currContext().write(ProofContext::MappingInv, cert, base, vt);
  }

  return mapping;
}

int targetCell(Bijection &mapping) {
  int cell = 0;
  int minSize = 0;
  int minCell = mapping.cells.size();
  while (cell < (int)mapping.cells.size()) {
    int cellSize = mapping.cells[cell] - cell;
    if (cellSize > 1 && (minSize == 0 || cellSize < minSize)) {
      minSize = cellSize;
      minCell = cell;
    }
    cell = mapping.cells[cell];
  }
  return minCell;
}

struct StabilizerEdge {
  int neighbor;
  int autIndex;
};

struct StabilizerGraph {
  vector<int> mcr;
  vector<vector<StabilizerEdge>> graph;

  explicit StabilizerGraph(int n) {
    mcr.resize(n);
    graph.resize(n);
  }
};

// The stabilizer graph will be a directed forest whose roots are MCRs
StabilizerGraph stabilizeProve(int n, vector<int> &node,
                               vector<vector<uintv>> &automorphisms) {
  vector<vector<StabilizerEdge>> graph(n);
  for (int j = 0; j < (int)automorphisms.size(); j++) {
    const auto &aut = automorphisms[j];
    bool stabilizes = true;
    for (int u : node)
      if (aut[u] != u) {
        stabilizes = false;
        break;
      }
    if (stabilizes)
      for (int i = 0; i < (int)aut.size(); i++)
        if (i != aut[i])
          graph[i].push_back({aut[i], j});
  }

  // Calculate MCRs and construct BFS forest
  StabilizerGraph S(n);
  for (int u = 0; u < n; u++)
    S.mcr[u] = u;

  queue<int> q;
  for (int u = 0; u < n; u++)
    if (S.mcr[u] == u) {
      q.push(u);
      while (!q.empty()) {
        int t = q.front();
        q.pop();
        for (auto edge : graph[t])
          if (S.mcr[edge.neighbor] != u) {
            S.mcr[edge.neighbor] = u;
            S.graph[t].push_back(edge);
            q.push(edge.neighbor);
          }
      }
    }

  return S;
}

void proveStabilizerOrbits(int u, uint32_t proofIndex, StabilizerGraph &S,
                           vector<uint32_t> &proofChildren, Proof &proof) {
  for (auto edge : S.graph[u]) {
    uint32_t proofIndexNeighbor =
        proof.writeSubstitution(proofIndex, edge.autIndex);
    proofChildren.push_back(proofIndexNeighbor);
    proveStabilizerOrbits(edge.neighbor, proofIndexNeighbor, S, proofChildren,
                          proof);
  }
}

void prove(vector<int> &node, Bijection mapping, vector<vector<uintv>> &graph,
           vector<vector<uintv>> &aut, Proof &proof) {

  int active_cell = 0;
  if (!node.empty())
    active_cell = distance(begin(mapping.u),
                           find(begin(mapping.u), end(mapping.u), node.back()));
  if (refineProve(mapping, graph, active_cell, proof))
    return;

  int target = targetCell(mapping);
  if (target == (int)graph.size()) {
    // Only reachable for the canonical node

    // Build an array of non-individualized vertex positions
    vector<bool> isIndividualized(graph.size());
    for (int u : node)
      isIndividualized[u] = true;
    vector<int> notIndividualized;
    for (int i = 0; i < (int)graph.size(); i++)
      if (!isIndividualized[mapping.u[i]])
        notIndividualized.push_back(i);

    // Prove monomials iteratively, starting from the full canonical bijection
    // monomial
    uint32_t prevMonomialIdx = proof.lookupTautology(RuleType::EXISO);
    while (!notIndividualized.empty()) {
      int i = notIndividualized.back();
      notIndividualized.pop_back();

      vector<Polynomial> cert(2);
      vector<uint32_t> base(2);

      cert[0] = {Monomial{1, {}}};
      base[0] = prevMonomialIdx;

      cert[1] = productFromIndices(mapping, notIndividualized, ff_order - 1);
      base[1] = proof.currContext().lookup(ProofContext::Mapping, mapping.u[i]);

      if (!notIndividualized.empty())
        prevMonomialIdx = proof.writeIdeal(cert, base);
      else
        proof.currContext().writeM(cert, base);
    }

    return;
  }

  vector<uint32_t> proofChildren;
  StabilizerGraph stabilizer = stabilizeProve(graph.size(), node, aut);

  int v = *min_element(begin(mapping.v) + target,
                       begin(mapping.v) + mapping.cells[target]);
  for (int i = target; i < mapping.cells[target]; i++) {

    if (mapping.u[i] != stabilizer.mcr[mapping.u[i]])
      continue;

    proof.pushContext(mapping.u[i], v, graph.size());

    node.push_back(mapping.u[i]);
    prove(node, individualizeProve(mapping, mapping.u[i], v, proof), graph, aut,
          proof);
    node.pop_back();

    proofChildren.push_back(proof.currContext().lookupM);

    // Prove stabilizer orbits using the newly calculated M
    proveStabilizerOrbits(mapping.u[i], proof.currContext().lookupM, stabilizer,
                          proofChildren, proof);

    proof.popContext();
  }

  // Prove internal node case
  vector<Polynomial> cert(proofChildren.size() + 1);
  vector<uint32_t> base(proofChildren.size() + 1);

  for (int i = 0; i < (int)proofChildren.size(); i++) {
    cert[i] = {Monomial{1, {}}};
    base[i] = proofChildren[i];
  }

  cert[proofChildren.size()] = {Monomial{(uintff)(ff_order - 1), {}}};
  base[proofChildren.size()] =
      proof.currContext().lookup(ProofContext::MappingInv, v);

  proof.currContext().writeM(cert, base);
}

vector<vector<uintv>> readGraph(string filename) {
  ifstream gin(filename);

  string s;
  gin >> s;
  while (s == "c") {
    gin.ignore(10000, '\n');
    gin >> s;
  }

  gin >> s;

  int n, m;
  gin >> n >> m;

  vector<vector<uintv>> graph(n);
  for (int i = 0; i < m; i++) {
    gin >> s;
    if (s == "e") {
      int a, b;
      gin >> a >> b;
      graph[a - 1].push_back(b - 1);
      graph[b - 1].push_back(a - 1);
    }
  }

  return graph;
}

vector<vector<uintv>> readAut(string filename, int graphSize) {
  ifstream ain(filename);

  int autCount;
  ain >> autCount;

  vector<vector<uintv>> automorphisms(autCount, vector<uintv>(graphSize));
  for (auto &aut : automorphisms)
    for (auto &x : aut)
      ain >> x;

  return automorphisms;
}

struct Options {
  // Mandatory
  string graphFile;
  string autFile;
  string proofFile;
  bool verbose = false;
  int graphSizeLimit = 4096;
  uint64_t memoryLimit = 0xffffffffull;
  bool inMemory = false;

  // Optional
  optional<string> statsFile;
};

optional<Options> handleOptions(int argc, char *argv[]) {
  if (argc < 4)
    return {};
  Options opts;
  opts.graphFile = string(argv[1]);
  opts.autFile = string(argv[2]);
  opts.proofFile = string(argv[3]);
  if (!filesystem::exists(filesystem::path(opts.graphFile))) {
    cerr << "Error: " << opts.graphFile << " does not exist" << endl;
    return {};
  }
  if (!filesystem::exists(filesystem::path(opts.autFile))) {
    cerr << "Error: " << opts.autFile << " does not exist" << endl;
    return {};
  }

  int i = 4;
  while (i < argc) {
    string opt = string(argv[i++]);

    bool noarg = false;
    if (opt == "-v" || opt == "--verbose") {
      opts.verbose = true;
      noarg = true;
    } else if (opt == "--in-memory") {
      opts.inMemory = true;
      noarg = true;
    }
    if (noarg)
      continue;

    if (i == argc)
      return {};

    if (opt == "-s" || opt == "--stats")
      opts.statsFile = string(argv[i++]);
    else if (opt == "-m" || opt == "--memory-limit")
      opts.memoryLimit = stoull(string(argv[i++]));
    else if (opt == "-g" || opt == "--vertex-limit") {
      opts.graphSizeLimit = stoi(string(argv[i++]));
      if (opts.graphSizeLimit > 4096) {
        cerr << "Error: Graph size limit cannot be greater than 4096" << endl;
        return {};
      }
    }
  }

  return opts;
}

struct Stats {
  int64_t fullRuleCount = -1;
  int64_t fullProofBytes = -1;
  int64_t prunedRuleCount = -1;
  int64_t prunedProofBytes = -1;
  int64_t proveTime = -1;
  int64_t pruneTime = -1;
  int64_t execTime = -1;
  int64_t memUsage = -1;
};

void jsonUint(string name, int64_t value, ofstream &out) {
  if (value >= 0)
    out << "\"" << name << "\":" << value << ", ";
}

void dumpStats(const Options &opts, const Stats &stats, string result) {
  ofstream sout(opts.statsFile.value());
  sout << "{";
  sout << "\"prove_input\":" << "\"" << opts.graphFile << "\"" << ", ";
  jsonUint("unpruned_rule_count", stats.fullRuleCount, sout);
  jsonUint("unpruned_proof_bytes", stats.fullProofBytes, sout);
  jsonUint("rule_count", stats.prunedRuleCount, sout);
  jsonUint("proof_bytes", stats.prunedProofBytes, sout);
  jsonUint("proof_gen_time", stats.proveTime, sout);
  jsonUint("proof_prune_time", stats.pruneTime, sout);
  jsonUint("prove_time", stats.execTime, sout);
  jsonUint("prove_memory", stats.memUsage, sout);
  sout << "\"prove_result\":\"" << result << "\"";
  sout << "}" << endl;
}

int main(int argc, char **argv) {
  auto optopts = handleOptions(argc, argv);
  if (!optopts.has_value()) {
    cerr << "Usage: ./prove graph_path aut_path output_path [options]" << endl;
    return 1;
  }
  auto opts = optopts.value();

  auto startTime = chrono::high_resolution_clock::now();

  vector<vector<uintv>> graph = readGraph(string(argv[1]));
  if (opts.verbose)
    cout << "Done reading graph!" << endl;

  vector<vector<uintv>> automorphisms = readAut(string(argv[2]), graph.size());
  if (opts.verbose)
    cout << "Done reading automorphisms!" << endl;

  vector<int> node;
  Bijection mapping(graph.size());

  Stats stats;

  if ((int)graph.size() > opts.graphSizeLimit) {
    cerr << "Graph size over " << opts.graphSizeLimit << " limit" << endl;
    dumpStats(opts, stats, "Graph too large");
    return 1;
  }

  if (opts.verbose)
    cout << "Preparing proof" << endl;
  Proof proof(graph.size(), opts.proofFile, opts.memoryLimit, opts.inMemory);

  uint32_t ruleCountBytesOffset = proof.inmemProof.size;
  uint32_t zero = 0;
  proof.write((char *)&zero, rule_idx_bytes); // this will be proof size

  proof.pushContext(graph.size());
  prove(node, mapping, graph, automorphisms, proof);
  proof.popContext();

  auto proofTime = chrono::high_resolution_clock::now();
  auto proofDuration =
      chrono::duration_cast<chrono::milliseconds>(proofTime - startTime);

  if (opts.verbose) {
    cout << "Proof generation finished in " << proofDuration.count() / 1000.0
         << " seconds" << endl;
    cout << "Proof rule count before pruning: " << proof.ruleCount << endl;
  }
  stats.fullRuleCount = proof.ruleCount;
  stats.fullProofBytes = proof.inmemProof.size;

  proof.compressAndCommit();

  auto pruneTime = chrono::high_resolution_clock::now();
  auto pruneDuration =
      chrono::duration_cast<chrono::milliseconds>(pruneTime - proofTime);

  if (opts.verbose) {
    cout << "Proof pruning finished in " << pruneDuration.count() / 1000.0
         << " seconds" << endl;
    cout << "Proof size in bytes: " << proof.inmemProof.size << endl;
    cout << "Proof rule count: " << proof.ruleCount << endl;
  }
  stats.prunedRuleCount = proof.ruleCount;
  stats.prunedProofBytes = proof.inmemProof.size;

  // Write final rule count into the mapped file
  proof.inmemProof.write((char *)&proof.ruleCount, rule_idx_bytes,
                         ruleCountBytesOffset);

  // If we generated in memory, commit to the file now
  if (opts.inMemory) {
    proof.inmemProof.commitToFile(opts.proofFile, proof.inmemProof.size);
  }

  auto execTime = chrono::high_resolution_clock::now();
  auto execDuration =
      chrono::duration_cast<chrono::milliseconds>(execTime - startTime);

  if (opts.statsFile.has_value()) {
    stats.proveTime = proofDuration.count();
    stats.pruneTime = pruneDuration.count();
    stats.execTime = execDuration.count();

    struct rusage usage;
    getrusage(RUSAGE_SELF, &usage);
    stats.memUsage = usage.ru_maxrss;
    dumpStats(opts, stats, "OK");
  }

  return 0;
}
