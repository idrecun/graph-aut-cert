#include <algorithm>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <fcntl.h>
#include <fstream>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <memory_resource>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>
#include <unordered_map>
#include <vector>

// ----- Util -----

template <typename T>
void verify(const T &ok, const char *reason = "verification failed") {
  if (!ok) [[unlikely]] {
    throw std::runtime_error(reason);
  }
}

constexpr size_t kScratchpadSize = 4ull * 1024 * 1024;         // 4 MB
constexpr size_t kPersistentSize = 32ull * 1024 * 1024 * 1024; // 32 GB

void *reserveAddressSpace(size_t size) {
  void *buffer = mmap(nullptr, size, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (buffer == MAP_FAILED) {
    throw std::runtime_error("Failed to reserve address space");
  }
  return buffer;
}

// ----- Finite field -----

constexpr uint16_t kFFOrder = 4099u; // Smallest prime above 4096

struct F4099 {
  uint16_t value;
};

F4099 operator+(const F4099 &a, const F4099 &b) {
  uint32_t sum = (uint32_t)a.value + b.value;
  if (sum >= kFFOrder) {
    sum -= kFFOrder;
  }
  return F4099{static_cast<uint16_t>(sum)};
}

F4099 operator-(const F4099 &a) {
  if (a.value == 0) {
    return F4099{0};
  }
  return F4099{static_cast<uint16_t>(kFFOrder - a.value)};
}

F4099 operator*(const F4099 &a, const F4099 &b) {
  uint32_t prod = (uint32_t)a.value * b.value;
  if (prod >= kFFOrder) {
    prod %= kFFOrder;
  }
  return F4099{static_cast<uint16_t>(prod)};
}

F4099 operator+=(F4099 &a, const F4099 &b) {
  a = a + b;
  return a;
}

bool operator==(const F4099 &a, const F4099 &b) { return a.value == b.value; }

bool operator!=(const F4099 &a, const F4099 &b) { return a.value != b.value; }

// ----- Graph and automorphisms -----

template <typename T> using Permutation = std::vector<T>;

template <typename T> bool isPermutation(const Permutation<T> &p) {
  std::vector<bool> used(p.size(), false);
  for (const auto &elem : p) {
    if (elem >= p.size() || used[elem]) {
      return false;
    }
    used[elem] = true;
  }
  return true;
}

using Vertex = uint16_t;
constexpr Vertex kMaxVertices = 4096;

using Automorphisms = std::vector<Permutation<Vertex>>;

struct Graph {
  Vertex vertexCount;
  std::vector<std::vector<bool>> adjacencyMatrix;
};

Graph parseGraph(std::istream &fin) {
  Graph g;
  bool parsedProblemLine = false;
  long long vertexCount = 0, edgeCount = 0, seenEdges = 0;
  std::string line;
  while (std::getline(fin, line)) {
    std::istringstream ss(line);
    std::string lineType;
    if (!(ss >> lineType)) {
      continue;
    }
    if (lineType == "p") {
      verify(!parsedProblemLine, "Multiple problem statement lines");
      parsedProblemLine = true;
      std::string edge, extra;
      ss >> edge >> vertexCount >> edgeCount;
      verify(!ss.fail(), "Error reading problem line");
      verify(!(ss >> extra), "Extra data in problem line");
      verify(edge == "edge", "Invalid problem line format");
      verify(vertexCount > 0 && vertexCount <= kMaxVertices,
             "Invalid number of vertices");
      verify(edgeCount >= 0, "Invalid number of edges");
      g.vertexCount = Vertex(vertexCount);
      g.adjacencyMatrix.assign(g.vertexCount,
                               std::vector<bool>(g.vertexCount, false));
    } else if (lineType == "e") {
      verify(parsedProblemLine, "Edge line before problem statement");
      std::string extra;
      long long u, v;
      ss >> u >> v;
      verify(!ss.fail(), "Error reading edge line");
      verify(!(ss >> extra), "Extra data in edge line");
      verify(u > 0 && u <= g.vertexCount, "Invalid vertex index");
      verify(v > 0 && v <= g.vertexCount, "Invalid vertex index");
      verify(u != v, "Graph loop detected");
      verify(!g.adjacencyMatrix[u - 1][v - 1], "Repeated edge detected");
      g.adjacencyMatrix[u - 1][v - 1] = g.adjacencyMatrix[v - 1][u - 1] = true;
      seenEdges++;
    } else if (lineType == "c") {
      continue;
    } else {
      throw std::runtime_error("Invalid line format in graph file");
    }
  }
  verify(!fin.bad(), "Error reading graph file");
  verify(parsedProblemLine, "Missing problem statement line");
  verify(edgeCount == seenEdges, "Edge count mismatch in graph file");
  return g;
}

bool isAutomorphism(const Graph &g, const Permutation<Vertex> &p) {
  if (p.size() != g.vertexCount)
    return false;

  for (uint32_t i = 0; i < g.vertexCount; i++) {
    for (uint32_t j = i + 1; j < g.vertexCount; j++) {
      if (g.adjacencyMatrix[i][j] != g.adjacencyMatrix[p[i]][p[j]]) {
        return false;
      }
    }
  }
  return true;
}

Automorphisms parseAutomorphisms(std::istream &fin, const Graph &g) {
  Automorphisms aut;
  long long count;
  fin >> count;
  verify(!fin.fail(), "Error reading automorphism count");
  verify(count > 0, "Invalid automorphism count");
  aut.reserve(count);
  for (long long i = 0; i < count; i++) {
    Permutation<Vertex> p;
    p.reserve(g.vertexCount);
    for (Vertex j = 0; j < g.vertexCount; j++) {
      long long v;
      fin >> v;
      verify(!fin.fail(), "Error reading automorphism");
      verify(v >= 0 && v < g.vertexCount, "Invalid vertex index");
      p.push_back(Vertex(v));
    }
    verify(isPermutation(p), "Not a permutation");
    verify(isAutomorphism(g, p), "Not an automorphism");
    aut.push_back(std::move(p));
  }
  std::string extra;
  verify(!(fin >> extra), "Extra data in automorphism file");
  verify(!fin.bad(), "Error reading automorphism file");
  return aut;
}

// ----- Polynomials -----

// Variable represents a variable with an exponent in a monomial. It contains
// the variable identifier in the 24 highest bits, and the exponent in the 8
// lowest bits.
using Variable = uint32_t;

constexpr Variable kVariableMask = 0xffffff00u;
constexpr Variable kExponentMask = 0x000000ffu;

Variable var(Variable p) { return p & kVariableMask; }
Variable exp(Variable p) { return p & kExponentMask; }
Vertex row(Variable v) { return (v >> 20) & 0xfff; }
Vertex col(Variable v) { return (v >> 8) & 0xfff; }
static_assert(kMaxVertices <= (1 << 12), "vertex index must fit in 12 bits");

Variable X(Vertex i, Vertex j, uint8_t e = 1) {
  return (Variable(i) << 20) | (Variable(j) << 8) | e;
}

Variable substitute(Variable x, const Permutation<Vertex> &a) {
  return (x & 0xfffff) | (Variable(a[row(x)]) << 20);
}

Variable safeAddVariables(Variable a, Variable b) {
  if (var(a) != var(b)) {
    throw std::invalid_argument("Addition of powers with different variables");
  }
  uint32_t exponentSum = exp(a) + exp(b);
  if (exponentSum > kExponentMask) {
    throw std::overflow_error("Variable addition overflow");
  }
  return var(a) | exponentSum;
}

using Variables = std::pmr::vector<Variable>;

template <typename F> struct Monomial {
  F coefficient;
  Variables variables;
};

template <typename F>
Monomial<F> mul(const Monomial<F> &a, const Monomial<F> &b,
                std::pmr::memory_resource *mr) {
  Monomial<F> result{
      .coefficient = a.coefficient * b.coefficient,
      .variables = Variables(mr),
  };
  result.variables.reserve(a.variables.size() + b.variables.size());
  auto i = begin(a.variables);
  auto j = begin(b.variables);
  while (i != end(a.variables) && j != end(b.variables)) {
    auto varA = var(*i);
    auto varB = var(*j);
    if (varA < varB) {
      result.variables.push_back(*i++);
    } else if (varA > varB) {
      result.variables.push_back(*j++);
    } else {
      result.variables.push_back(safeAddVariables(*i++, *j++));
    }
  }
  result.variables.insert(end(result.variables), i, end(a.variables));
  result.variables.insert(end(result.variables), j, end(b.variables));
  return result;
}

template <typename F>
Monomial<F> newMonomial(F coefficient, Variables &&variables) {
  Monomial<F> m{.coefficient = coefficient, .variables = std::move(variables)};
  std::sort(begin(m.variables), end(m.variables));
  if (!isMonomial(m)) {
    throw std::invalid_argument("invalid monomial variables");
  }
  return m;
}

template <typename F> bool isMonomial(const Monomial<F> &m) {
  for (size_t i = 1; i < m.variables.size(); i++) {
    if (!(var(m.variables[i - 1]) < var(m.variables[i]))) {
      return false;
    }
  }
  return m.coefficient != F{};
}

struct VariablesHash {
  std::size_t operator()(const Variables &v) const {
    return std::hash<std::string_view>()(std::string_view(
        reinterpret_cast<const char *>(v.data()), v.size() * sizeof(Variable)));
  }
};

template <typename F> using Polynomial = std::pmr::vector<Monomial<F>>;

template <typename F>
void addTerm(Polynomial<F> &p, std::initializer_list<Variable> vars) {
  p.push_back(
      newMonomial<F>(F{1}, Variables(vars, p.get_allocator().resource())));
}

template <typename F> void addTerm(Polynomial<F> &p, Variables &&vars) {
  p.push_back(newMonomial<F>(F{1}, std::move(vars)));
}

template <typename F>
void subTerm(Polynomial<F> &p, std::initializer_list<Variable> vars) {
  p.push_back(
      newMonomial<F>(-F{1}, Variables(vars, p.get_allocator().resource())));
}

template <typename F>
Polynomial<F> combine(const std::pmr::vector<const Polynomial<F> *> &cert,
                      const std::pmr::vector<const Polynomial<F> *> &base,
                      std::pmr::memory_resource *persistent,
                      std::pmr::memory_resource *scratch) {
  if (cert.size() != base.size()) {
    throw std::invalid_argument("cert and base must have the same size");
  }
  size_t allocSize = 0;
  for (size_t i = 0; i < cert.size(); ++i) {
    allocSize += cert[i]->size() * base[i]->size();
  }
  std::pmr::unordered_map<Variables, F, VariablesHash> coefficients(scratch);
  coefficients.reserve(allocSize);
  for (size_t i = 0; i < cert.size(); ++i) {
    for (const auto &m1 : *cert[i]) {
      for (const auto &m2 : *base[i]) {
        auto [coefficient, variables] = mul(m1, m2, scratch);
        coefficients[std::move(variables)] += coefficient;
      }
    }
  }
  Polynomial<F> result(persistent);
  result.reserve(coefficients.size());
  for (const auto &[variables, coefficient] : coefficients) {
    if (coefficient != F{}) {
      result.push_back(Monomial<F>{
          .coefficient = coefficient,
          .variables = Variables(variables, persistent),
      });
    }
  }
  return result;
}

Polynomial<F4099> substitute(const Polynomial<F4099> &p,
                             const Permutation<Vertex> &a,
                             std::pmr::memory_resource *mr) {
  Polynomial<F4099> result(mr);
  result.reserve(p.size());
  for (const Monomial<F4099> &m : p) {
    Variables vars(mr);
    vars.reserve(m.variables.size());
    for (const Variable &v : m.variables) {
      vars.push_back(substitute(v, a));
    }
    result.emplace_back(newMonomial<F4099>(m.coefficient, std::move(vars)));
  }
  return result;
}

// ----- Proof verification -----

static_assert(std::endian::native == std::endian::little,
              "proof files are little-endian");

struct Reader {
  char *data;
  size_t position;
  size_t fileSize;

  void read(char *buffer, size_t size) {
    if (position + size > fileSize) {
      throw std::runtime_error("Reading out of bounds of file");
    }
    memcpy(buffer, data + position, size);
    position += size;
  }

  bool eof() const { return position == fileSize; }
};

Reader newReader(const std::string &filename) {
  int fd = open(filename.c_str(), O_RDONLY);
  if (fd < 0) {
    throw std::runtime_error("Failed to open file");
  }
  struct stat st;
  if (fstat(fd, &st) < 0) {
    close(fd);
    throw std::runtime_error("Failed to stat file");
  }
  size_t fileSize = st.st_size;
  char *data = (char *)mmap(nullptr, fileSize, PROT_READ, MAP_PRIVATE, fd, 0);
  close(fd);
  if (data == MAP_FAILED) {
    throw std::runtime_error("Failed to mmap file");
  }
  return Reader{.data = data, .position = 0, .fileSize = fileSize};
}

using Facts = std::pmr::vector<Polynomial<F4099>>;

struct Verifier {
  Reader *reader;

  std::pmr::monotonic_buffer_resource persistent{
      reserveAddressSpace(kPersistentSize), kPersistentSize,
      std::pmr::null_memory_resource()};

  std::vector<std::byte> scratchBuffer =
      std::vector<std::byte>(kScratchpadSize);

  template <typename T> void read(T &t) { reader->read((char *)&t, sizeof(T)); }

  template <typename T> void parseLessThan(T &t, const T &limit) {
    read(t);
    verify(t < limit, "value out of bounds");
  }

  void parseVertex(Vertex &u, const Graph &g) {
    parseLessThan(u, g.vertexCount);
  }

  void parseVariable(Variable &v, const Graph &g) {
    read(v);
    verify(exp(v) != 0, "variable exponent cannot be zero");
    verify(row(v) < g.vertexCount, "variable first vertex out of bounds");
    verify(col(v) < g.vertexCount, "variable second vertex out of bounds");
  }

  void parseField(F4099 &f) { parseLessThan(f.value, kFFOrder); }

  Monomial<F4099> parseMonomial(const Graph &g, std::pmr::memory_resource *mr) {
    Monomial<F4099> m{.coefficient = {}, .variables = Variables(mr)};
    uint16_t variableCount;
    read(variableCount);
    m.variables.reserve(variableCount);
    for (uint16_t i = 0; i < variableCount; i++) {
      Variable v;
      parseVariable(v, g);
      m.variables.push_back(v);
    }
    parseField(m.coefficient);
    verify(isMonomial(m), "monomial check failed");
    return m;
  }

  Polynomial<F4099> parsePolynomial(const Graph &g,
                                    std::pmr::memory_resource *mr) {
    Polynomial<F4099> p(mr);
    uint16_t monomialCount;
    read(monomialCount);
    p.reserve(monomialCount);
    for (uint16_t i = 0; i < monomialCount; i++) {
      p.push_back(parseMonomial(g, mr));
    }
    return p;
  }

  Polynomial<F4099> newPolynomial(size_t terms) {
    Polynomial<F4099> p(&persistent);
    p.reserve(terms);
    return p;
  }

  Polynomial<F4099> ruleIdeal(const Graph &g, const Facts &facts,
                              std::pmr::memory_resource *scratch) {
    uint16_t size;
    read(size);

    std::pmr::vector<const Polynomial<F4099> *> polynomials(scratch);
    polynomials.reserve(size);
    for (uint16_t i = 0; i < size; i++) {
      uint32_t factIndex;
      parseLessThan<uint32_t>(factIndex, facts.size());
      polynomials.push_back(&facts[factIndex]);
    }

    std::pmr::vector<Polynomial<F4099>> certificate(scratch);
    certificate.reserve(size);
    for (uint16_t i = 0; i < size; i++) {
      certificate.push_back(parsePolynomial(g, scratch));
    }

    std::pmr::vector<const Polynomial<F4099> *> certificateRefs(scratch);
    certificateRefs.reserve(certificate.size());
    for (const Polynomial<F4099> &poly : certificate) {
      certificateRefs.push_back(&poly);
    }

    return combine(certificateRefs, polynomials, &persistent, scratch);
  }

  Polynomial<F4099> ruleRowNZ(const Graph &g) {
    Vertex i, j, k;
    parseVertex(i, g);
    parseVertex(j, g);
    parseVertex(k, g);
    verify(j < k, "row-non-zero: j must be less than k");
    // RowNZ_{i; j, k} = x_{i,j} x_{i,k}
    Polynomial<F4099> p = newPolynomial(1);
    addTerm(p, {X(i, j), X(i, k)});
    return p;
  }

  Polynomial<F4099> ruleColNZ(const Graph &g) {
    Vertex i, j, k;
    parseVertex(i, g);
    parseVertex(j, g);
    parseVertex(k, g);
    verify(i < j, "col-non-zero: i must be less than j");
    // ColNZ_{i, j; k} = x_{i,k} x_{j,k}
    Polynomial<F4099> p = newPolynomial(1);
    addTerm(p, {X(i, k), X(j, k)});
    return p;
  }

  Polynomial<F4099> ruleRowS(const Graph &g) {
    Vertex i;
    parseVertex(i, g);
    // RowS_i = -1 + sum_j x_{i,j}
    Polynomial<F4099> p = newPolynomial(1 + g.vertexCount);
    subTerm(p, {});
    for (Vertex j = 0; j < g.vertexCount; j++) {
      addTerm(p, {X(i, j)});
    }
    return p;
  }

  Polynomial<F4099> ruleColS(const Graph &g) {
    Vertex j;
    parseVertex(j, g);
    // ColS_j = -1 + sum_i x_{i,j}
    Polynomial<F4099> p = newPolynomial(1 + g.vertexCount);
    subTerm(p, {});
    for (Vertex i = 0; i < g.vertexCount; i++) {
      addTerm(p, {X(i, j)});
    }
    return p;
  }

  Polynomial<F4099> ruleIso(const Graph &g) {
    Vertex i, j;
    parseVertex(i, g);
    parseVertex(j, g);
    // Iso_{i,j} = (AX - XA)_{i,j}
    //           = sum_{k adjacent to i} x_{k,j} - sum_{k adjacent to j} x_{i,k}
    size_t size = 0;
    for (Vertex k = 0; k < g.vertexCount; k++) {
      size +=
          (g.adjacencyMatrix[i][k] ? 1 : 0) + (g.adjacencyMatrix[k][j] ? 1 : 0);
    }
    Polynomial<F4099> p = newPolynomial(size);
    for (Vertex k = 0; k < g.vertexCount; k++) {
      if (g.adjacencyMatrix[i][k]) {
        addTerm(p, {X(k, j)});
      }
    }
    for (Vertex k = 0; k < g.vertexCount; k++) {
      if (g.adjacencyMatrix[k][j]) {
        subTerm(p, {X(i, k)});
      }
    }
    return p;
  }

  Polynomial<F4099> ruleExIso(const Graph &g, const Automorphisms &aut) {
    uint32_t index;
    parseLessThan<uint32_t>(index, aut.size());
    // ExIso_a = prod_u x_{u, a(u)}
    Variables variables(&persistent);
    variables.reserve(g.vertexCount);
    for (Vertex i = 0; i < g.vertexCount; i++) {
      variables.push_back(X(i, aut[index][i]));
    }
    Polynomial<F4099> p = newPolynomial(1);
    addTerm(p, std::move(variables));
    return p;
  }

  Polynomial<F4099> ruleBin(const Graph &g) {
    Vertex i, j;
    parseVertex(i, g);
    parseVertex(j, g);
    // Bin_{i,j} = x_{i,j}^2 - x_{i,j}
    Polynomial<F4099> p = newPolynomial(2);
    addTerm(p, {X(i, j, 2)});
    subTerm(p, {X(i, j)});
    return p;
  }

  Polynomial<F4099> ruleSubstitution(const Facts &facts,
                                     const Automorphisms &aut) {
    uint32_t factIndex, autIndex;
    parseLessThan<uint32_t>(factIndex, facts.size());
    parseLessThan<uint32_t>(autIndex, aut.size());
    return substitute(facts[factIndex], aut[autIndex], &persistent);
  }

  void rule(const Graph &g, const Automorphisms &aut, Facts &facts) {
    uint8_t type;
    read(type);

    std::pmr::monotonic_buffer_resource scratch(scratchBuffer.data(),
                                                scratchBuffer.size());

    if (type == 0) {
      facts.emplace_back(ruleIdeal(g, facts, &scratch));
    } else if (type == 1) {
      facts.emplace_back(ruleSubstitution(facts, aut));
    } else if (type == 2) {
      facts.emplace_back(ruleRowNZ(g));
    } else if (type == 3) {
      facts.emplace_back(ruleColNZ(g));
    } else if (type == 4) {
      facts.emplace_back(ruleRowS(g));
    } else if (type == 5) {
      facts.emplace_back(ruleColS(g));
    } else if (type == 6) {
      facts.emplace_back(ruleIso(g));
    } else if (type == 7) {
      facts.emplace_back(ruleExIso(g, aut));
    } else if (type == 8) {
      facts.emplace_back(ruleBin(g));
    } else {
      verify(false, "invalid rule type");
    }
  }

  void verifyProof(const Graph &g, const Automorphisms &aut) {
    uint32_t proofLength;
    read(proofLength);
    verify(proofLength > 0, "proof length must be positive");

    Facts facts(&persistent);
    facts.reserve(proofLength);
    for (uint32_t i = 0; i < proofLength; i++) {
      rule(g, aut, facts);
    }
    verify(reader->eof(), "extra data in stream");
    verify(facts.size() == proofLength, "proof length mismatch");
    const Polynomial<F4099> &last = facts.back();
    verify(last.size() == 1 && last[0].variables.empty() &&
               last[0].coefficient == F4099{1},
           "not a nullstellensatz proof");
  }
};

// ----- Main -----

int main(int argc, char **argv) {
  if (argc != 5) {
    std::cerr << "Usage: " << argv[0]
              << " <proof_file> <graph_file> <auts_file> <output_file>"
              << std::endl;
    return 1;
  }
  std::string proofFile = std::string(argv[1]);
  std::string graphFile = std::string(argv[2]);
  std::string autsFile = std::string(argv[3]);
  std::string outputFile = std::string(argv[4]);

  auto startTime = std::chrono::high_resolution_clock::now();

  bool ok = true;
  std::string errorMsg;
  try {
    std::ifstream graphInput(graphFile);
    verify(graphInput.is_open(), "Failed to open graph file");
    Graph graph = parseGraph(graphInput);

    std::ifstream autsInput(autsFile);
    verify(autsInput.is_open(), "Failed to open automorphisms file");
    Automorphisms auts = parseAutomorphisms(autsInput, graph);

    Reader reader = newReader(proofFile);
    Verifier verifier{.reader = &reader};
    verifier.verifyProof(graph, auts);
  } catch (const std::exception &e) {
    ok = false;
    errorMsg = e.what();
  }

  auto endTime = std::chrono::high_resolution_clock::now();
  auto execDuration = std::chrono::duration_cast<std::chrono::milliseconds>(
      endTime - startTime);

  struct rusage usage;
  getrusage(RUSAGE_SELF, &usage);

  std::ofstream sout(outputFile);
  sout << "{";
  sout << "\"verify_input\":" << "\"" << proofFile << "\"" << ", ";
  sout << "\"verify_time\":" << execDuration.count() << ", ";
  sout << "\"verify_memory\":" << usage.ru_maxrss << ", ";
  sout << "\"verify_result\":\"" << (ok ? "OK" : "Failed") << "\"";
  sout << "}" << std::endl;

  if (!ok) {
    std::cerr << "Error: " << errorMsg << std::endl;
    return 1;
  }

  std::cout << "OK" << std::endl;
  return 0;
}
