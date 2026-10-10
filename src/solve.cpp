#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <queue>
#include <filesystem>
#include <chrono>

using namespace std;

vector< vector<int> > readGraph(string filename) {
    ifstream fin(filename);

    string s;
    fin >> s;
    while(s == "c") {
        fin.ignore(10000, '\n');
        fin >> s;
    }

    fin >> s;

    int n, m;
    fin >> n >> m;

    vector< vector<int> > graph(n);
    for(int i = 0; i < m; i++) {
        fin >> s;
        if(s == "e") {
            int a, b;
            fin >> a >> b;
            graph[a-1].push_back(b-1);
            graph[b-1].push_back(a-1);
        }
    }
    return graph;
}

struct bijection {
    vector<int> u;
    vector<int> v;
    vector<int> cells;
    int cell_count;
};

void print_bijection(bijection& mapping) {
    for(int cell = 0; cell < (int)mapping.cells.size(); cell = mapping.cells[cell]) {
        cout << "{ ";
        for(int i = cell; i < mapping.cells[cell]; i++)
            cout << mapping.u[i] << ' ';
        cout << "}";
    }
    cout << " -> ";
    for(int cell = 0; cell < (int)mapping.cells.size(); cell = mapping.cells[cell]) {
        cout << "{ ";
        for(int i = cell; i < mapping.cells[cell]; i++)
            cout << mapping.v[i] << ' ';
        cout << "}";
    }
    cout << endl;
}

bool split(bijection& mapping, vector< vector<int> >& graph, int W, queue<int>& active_cells) {
    vector<int> uDeg(graph.size()), vDeg(graph.size());
    for(int i = W; i < mapping.cells[W]; i++) {
        for(int un : graph[mapping.u[i]])
            uDeg[un]++;
        for(int vn : graph[mapping.v[i]])
            vDeg[vn]++;
    }

    for(int i = 0; i < (int)graph.size(); i = mapping.cells[i]) {
        sort(begin(mapping.u) + i, begin(mapping.u) + mapping.cells[i],
            [&](int a, int b){ return make_pair(uDeg[a], a) < make_pair(uDeg[b], b); });
        sort(begin(mapping.v) + i, begin(mapping.v) + mapping.cells[i],
            [&](int a, int b){ return make_pair(vDeg[a], a) < make_pair(vDeg[b], b); });
    }

    for(int i = 0; i < (int)graph.size(); i++)
        if(uDeg[mapping.u[i]] != vDeg[mapping.v[i]])
            return true; // is weak

    for(int i = 0; i < (int)graph.size(); i = mapping.cells[i]) {
        int prev = i;
        for(int j = i + 1; j < mapping.cells[i]; j++)
            if(uDeg[mapping.u[j]] != uDeg[mapping.u[j-1]]) {
                mapping.cell_count++;
                mapping.cells[j] = mapping.cells[prev];
                mapping.cells[prev] = j;
                prev = j;

                active_cells.push(j);
            }
    }
    return false;
}

bool refine(bijection& mapping, vector< vector<int> >& graph, int first_active_cell) {
    queue<int> active_cells;
    active_cells.push(first_active_cell);
    while(!active_cells.empty() && mapping.cell_count < (int)graph.size()) {
        int W = active_cells.front();
        active_cells.pop();

        if(split(mapping, graph, W, active_cells))
            return true;
    }
    return false;
}

bijection individualize(bijection mapping, int u, int v) {
    int i = find(begin(mapping.u), end(mapping.u), u) - begin(mapping.u);
    int j = find(begin(mapping.v), end(mapping.v), v) - begin(mapping.v);

    int cell = 0;
    while(mapping.cells[cell] <= i)
        cell = mapping.cells[cell];

    while(i > cell) {
        swap(mapping.u[i], mapping.u[i - 1]);
        i--;
    }
    while(j > cell) {
        swap(mapping.v[j], mapping.v[j - 1]);
        j--;
    }

    mapping.cells[cell + 1] = mapping.cells[cell];
    mapping.cells[cell] = cell + 1;
    return mapping;
}

int target_cell(bijection& mapping) {
    int cell = 0;
    int minSize = 0;
    int minCell = mapping.cells.size();
    while(cell < (int)mapping.cells.size()) {
        int cellSize = mapping.cells[cell] - cell;
        if(cellSize > 1 && (minSize == 0 || cellSize < minSize)) {
            minSize = cellSize;
            minCell = cell;
        }
        cell = mapping.cells[cell];
    }
    return minCell;
}

struct dsu {
    vector<int> rank;
    vector<int> parent;
    vector<int> rep;

    dsu(int n) {
        rank.resize(n, 1);
        parent.resize(n);
        rep.resize(n);
        for(int i = 0; i < n; i++)
            rep[i] = parent[i] = i;
    }

    int find(int u) {
        while(parent[u] != u)
            u = parent[u];
        return u;
    }

    int mcr(int u) {
        return rep[find(u)];
    }

    void merge(int u, int v) {
        u = find(u);
        v = find(v);
        if(u == v)
            return;
        if(rank[u] < rank[v]) {
            parent[u] = v;
            rank[v] += rank[u];
            rep[v] = min(rep[v], rep[u]);
        }
        else {
            parent[v] = u;
            rank[u] += rank[v];
            rep[u] = min(rep[u], rep[v]);
        }
    }
};

vector< vector<int> > aut_gen;

void stabilize(dsu& orbit_partition, vector<int>& node, int& start_index) {
    for(int j = start_index; j < (int)aut_gen.size(); j++) {
        auto& aut = aut_gen[j];
        bool stabilizes = true;
        for(int u : node)
            if(aut[u] != u) {
                stabilizes = false;
                break;
            }
        if(stabilizes)
            for(int i = 0; i < (int)aut.size(); i++)
                orbit_partition.merge(i, aut[i]);
    }
}

vector<int> canon_node;
bijection canon_map;

// returns backjump level
int search(vector<int>& node, bijection mapping, vector< vector<int> >& graph) {

    int active_cell = 0;
    if(!node.empty())
        active_cell = find(begin(mapping.u), end(mapping.u), node.back()) - begin(mapping.u);
    if(refine(mapping, graph, active_cell))
        return node.size();

    int target = target_cell(mapping);
    if(target == (int)graph.size()) {
        if(canon_map.cells.empty()) { // detect canonical node
            canon_map = mapping;
            canon_node = node;
        }

        // detect automorphism (including identity)
        vector<int> aut(graph.size());
        for(int i = 0; i < (int)graph.size(); i++)
            aut[canon_map.u[i]] = mapping.u[i];
        aut_gen.push_back(aut);

        int backjump = 0;
        while(backjump < (int)canon_node.size() && canon_node[backjump] == node[backjump])
            backjump++;
        return backjump;
    }

    dsu stabilizer(graph.size());
    int aut_index = 0;

    int v = *min_element(begin(mapping.v) + target, begin(mapping.v) + mapping.cells[target]);
    for(int i = target; i < mapping.cells[target]; i++) {
        stabilize(stabilizer, node, aut_index);
        if(mapping.u[i] != stabilizer.mcr(mapping.u[i]))
            continue;
        node.push_back(mapping.u[i]);
        int backjump = search(node, individualize(mapping, mapping.u[i], v), graph);
        node.pop_back();

        if(backjump < (int)node.size())
            return backjump;
    }
    return node.size();
}

struct Options {
    // Mandatory
    string inputFile;
    string outputFile;

    // Optional
    optional<string> statsFile;
    optional<int> graphVertexLimit;
};

optional<Options> handleOptions(int argc, char* argv[]) {
    if(argc < 3)
        return {};
    Options opts;
    opts.inputFile = string(argv[1]);
    opts.outputFile = string(argv[2]);
    if(!filesystem::exists(filesystem::path(opts.inputFile))) {
        cerr << "Error: " << opts.inputFile << " does not exist" << endl;
        return {};
    }

    int i = 3;
    while(i < argc) {
        string opt = string(argv[i++]);

        if(i == argc)
            return {};

        if(opt == "-s" || opt == "--stats")
            opts.statsFile = string(argv[i++]);
        else if(opt == "-l" || opt == "--vertex-limit")
            opts.graphVertexLimit = stoi(string(argv[i++]));
    }

    return opts;
}

void dumpStats(const Options& opts, int64_t execTime, int graphSize, int autSize, string result) {
    ofstream sout(opts.statsFile.value());
    sout << "{";
    sout << "\"solve_input\":" << "\"" << opts.inputFile << "\"" << ", ";
    if (execTime >= 0) sout << "\"solve_time\":" << execTime << ", ";
    if (graphSize >= 0) sout << "\"graph_size\":" << graphSize << ", ";
    if (autSize >= 0) sout << "\"aut_size\":" << autSize << ", ";
    sout << "\"solve_result\":\"" << result << "\"";
    sout << "}" << endl;
}

int main(int argc, char* argv[]) {
    auto optopts = handleOptions(argc, argv);
    if (!optopts.has_value()) {
        cerr << "Usage: ./solve input_path output_path [options]" << endl;
        return 1;
    }
    auto opts = optopts.value();

    auto startTime = chrono::high_resolution_clock::now();

    vector<vector<int> > graph = readGraph(opts.inputFile);
    if(opts.graphVertexLimit.has_value() && (int)graph.size() > opts.graphVertexLimit.value()) {
        cout << "Graph vertex count over limit" << endl;
        if(opts.statsFile.has_value())
            dumpStats(opts, -1, graph.size(), -1, "Graph too large");
        return 1;
    }
    vector<int> node;

    bijection mapping;
    mapping.u = vector<int>(graph.size());
    for (int i = 0; i < (int)graph.size(); i++)
        mapping.u[i] = i;
    mapping.v = vector<int>(graph.size());
    for (int i = 0; i < (int)graph.size(); i++)
        mapping.v[i] = i;
    mapping.cells = vector<int>(graph.size());
    mapping.cells[0] = graph.size();
    mapping.cell_count = 1;

    search(node, mapping, graph);

    ofstream fout(opts.outputFile);

    fout << aut_gen.size() << endl;
    for (auto &aut: aut_gen) {
        for (auto &p: aut)
            fout << p << ' ';
        fout << endl;
    }

    auto endTime = chrono::high_resolution_clock::now();
    auto execDuration = chrono::duration_cast<chrono::milliseconds>(endTime - startTime);

    if(opts.statsFile.has_value())
        dumpStats(opts, execDuration.count(), graph.size(), aut_gen.size(), "OK");

    return 0;
}
