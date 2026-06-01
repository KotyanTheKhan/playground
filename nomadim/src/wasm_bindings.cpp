// WebAssembly bindings for libnomadim (compiled only under -DNOMADIM_WASM=ON).
// String-in/string-out bridge: JSON at the boundary, YAML for documents. yaml-cpp
// parses JSON (a YAML subset) for inputs; outputs are emitted by hand.
#include <emscripten/bind.h>
#include "nomadim/io.hpp"
#include "nomadim/poset.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/realizer.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/types.hpp"
#include <yaml-cpp/yaml.h>
#include <sstream>
#include <string>
#include <vector>

using namespace nomadim;

namespace {

adjacency_list parse_adjacency(const std::string& json) {
    YAML::Node n = YAML::Load(json);
    adjacency_list g;
    for (const auto& row : n) {
        std::vector<int> succ;
        for (const auto& v : row) succ.push_back(v.as<int>());
        g.push_back(std::move(succ));
    }
    return g;
}

std::string ints_to_json(const std::vector<int>& xs) {
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < xs.size(); ++i) { if (i) os << ','; os << xs[i]; }
    os << ']';
    return os.str();
}

std::string adjacency_to_json(const adjacency_list& g) {
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < g.size(); ++i) { if (i) os << ','; os << ints_to_json(g[i]); }
    os << ']';
    return os.str();
}

Execution parse_execution(const YAML::Node& n) {
    Execution e;
    e.n_procs = n["n_procs"].as<int>();
    if (n["syncs"])
        for (const auto& s : n["syncs"]) e.syncs.push_back({s[0].as<int>(), s[1].as<int>()});
    e.validate();
    return e;
}

std::string syncs_to_json(const std::vector<std::pair<int,int>>& syncs) {
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < syncs.size(); ++i) {
        if (i) os << ',';
        os << '[' << syncs[i].first << ',' << syncs[i].second << ']';
    }
    os << ']';
    return os.str();
}

bool is_dim2_json(const std::string& adj_json) {
    return is_dim2(parse_adjacency(adj_json));
}

std::string find_realizer_json(const std::string& adj_json) {
    Realizer r = find_realizer(parse_adjacency(adj_json));
    std::ostringstream os;
    os << "{\"dim_le_2\":" << (r.dim_le_2 ? "true" : "false")
       << ",\"l1\":" << ints_to_json(r.l1)
       << ",\"l2\":" << ints_to_json(r.l2) << "}";
    return os.str();
}

std::string critical_pairs_json(const std::string& adj_json) {
    adjacency_list g = parse_adjacency(adj_json);
    int n = (int)g.size();
    std::vector<int> m = make_graph_matrix(g);
    auto cps = find_critical_pairs(m.data(), n);
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < cps.size(); ++i) {
        if (i) os << ',';
        os << '[' << cps[i].x << ',' << cps[i].y << ']';
    }
    os << ']';
    return os.str();
}

std::string expand_execution_json(const std::string& exec_json) {
    Execution e = parse_execution(YAML::Load(exec_json));
    ProcessGraph g = ProcessGraph::build(e);
    Poset p = Poset::from(g);
    std::ostringstream os;
    os << "{\"n_vertices\":" << p.n_vertices
       << ",\"edges\":" << adjacency_to_json(p.edges) << "}";
    return os.str();
}

std::string parse_document_json(const std::string& text) {
    Document d = parse_document(text);
    std::ostringstream os;
    os << '{';
    bool first = true;
    if (d.execution) {
        os << "\"execution\":{\"n_procs\":" << d.execution->n_procs
           << ",\"syncs\":" << syncs_to_json(d.execution->syncs) << "}";
        first = false;
    }
    if (d.poset) {
        if (!first) os << ',';
        os << "\"poset\":{\"n_vertices\":" << d.poset->n_vertices
           << ",\"edges\":" << adjacency_to_json(d.poset->edges) << "}";
    }
    os << '}';
    return os.str();
}

std::string dump_poset_json(const std::string& poset_json) {
    YAML::Node n = YAML::Load(poset_json);
    Poset p;
    p.n_vertices = n["n_vertices"].as<int>();
    p.edges.assign(p.n_vertices, {});
    const YAML::Node& edges = n["edges"];
    for (int u = 0; u < (int)edges.size() && u < p.n_vertices; ++u)
        for (const auto& v : edges[u]) p.edges[u].push_back(v.as<int>());
    p.validate();
    return dump_poset(p);
}

std::string dump_execution_json(const std::string& exec_json) {
    Execution e = parse_execution(YAML::Load(exec_json));
    return dump_execution(e);
}

std::string lib_version() { return std::string(version()); }

} // namespace

EMSCRIPTEN_BINDINGS(nomadim_module) {
    emscripten::function("isDim2", &is_dim2_json);
    emscripten::function("findRealizer", &find_realizer_json);
    emscripten::function("criticalPairs", &critical_pairs_json);
    emscripten::function("expandExecution", &expand_execution_json);
    emscripten::function("parseDocument", &parse_document_json);
    emscripten::function("dumpPoset", &dump_poset_json);
    emscripten::function("dumpExecution", &dump_execution_json);
    emscripten::function("version", &lib_version);
}
