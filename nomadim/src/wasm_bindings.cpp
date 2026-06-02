// WebAssembly bindings for libnomadim (compiled only under -DNOMADIM_WASM=ON).
// String-in/string-out bridge: JSON at the boundary, YAML for documents. yaml-cpp
// parses JSON (a YAML subset) for inputs; outputs are emitted by hand.
#include <emscripten/bind.h>
#include "nomadim/io.hpp"
#include "nomadim/poset.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/hypergraph.hpp"
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

// Build an adjacency_list from JSON and validate it as a poset (endpoint bounds
// + acyclicity), matching the CLI, which never runs an algorithm on an
// unvalidated poset. Throws std::invalid_argument on malformed input.
adjacency_list parse_validated_adjacency(const std::string& json) {
    adjacency_list g = parse_adjacency(json);
    Poset p;
    p.n_vertices = (int)g.size();
    p.edges = g;
    p.validate();
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

std::string realizer_to_json(const std::vector<std::vector<int>>& realizer) {
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < realizer.size(); ++i) { if (i) os << ','; os << ints_to_json(realizer[i]); }
    os << ']';
    return os.str();
}

Caps parse_caps(const std::string& json) {
    Caps caps;
    if (json.empty()) return caps;
    YAML::Node n = YAML::Load(json);
    if (n["max_vertices"])       caps.max_vertices = n["max_vertices"].as<int>();
    if (n["max_critical_pairs"]) caps.max_critical_pairs = n["max_critical_pairs"].as<int>();
    if (n["max_results"])        caps.max_results = n["max_results"].as<int>();
    return caps;
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
    return is_dim2(parse_validated_adjacency(adj_json));
}

std::string find_realizer_json(const std::string& adj_json) {
    Realizer r = find_realizer(parse_validated_adjacency(adj_json));
    std::ostringstream os;
    os << "{\"dim_le_2\":" << (r.dim_le_2 ? "true" : "false")
       << ",\"l1\":" << ints_to_json(r.l1)
       << ",\"l2\":" << ints_to_json(r.l2) << "}";
    return os.str();
}

std::string critical_pairs_json(const std::string& adj_json) {
    adjacency_list g = parse_validated_adjacency(adj_json);
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

std::string dimension_json(const std::string& adj_json, const std::string& caps_json) {
    try {
        adjacency_list g = parse_validated_adjacency(adj_json);
        DimensionResult dr = analyze_dimension(g, parse_caps(caps_json));
        std::ostringstream os;
        os << "{\"dimension\":" << dr.dimension << ",\"criticalPairs\":[";
        for (size_t i = 0; i < dr.critical_pairs.size(); ++i)
            os << (i ? "," : "") << '[' << dr.critical_pairs[i].x << ',' << dr.critical_pairs[i].y << ']';
        os << "],\"hyperedges\":[";
        for (size_t i = 0; i < dr.hyperedges.size(); ++i)
            os << (i ? "," : "") << ints_to_json(dr.hyperedges[i]);
        os << "]}";
        return os.str();
    } catch (const std::exception& e) {
        return std::string("{\"error\":\"") + e.what() + "\"}";
    }
}

std::string find_one_realizer_json(const std::string& adj_json, const std::string& caps_json) {
    try {
        adjacency_list g = parse_validated_adjacency(adj_json);
        DimensionResult dr = analyze_dimension(g, parse_caps(caps_json));
        std::ostringstream os;
        os << "{\"dimension\":" << dr.dimension << ",\"realizer\":"
           << (dr.colorings.empty() ? "[]" : realizer_to_json(dr.colorings.front().realizer)) << "}";
        return os.str();
    } catch (const std::exception& e) {
        return std::string("{\"error\":\"") + e.what() + "\"}";
    }
}

std::string all_realizers_json(const std::string& adj_json, const std::string& caps_json) {
    try {
        adjacency_list g = parse_validated_adjacency(adj_json);
        DimensionResult dr = analyze_dimension(g, parse_caps(caps_json));
        std::ostringstream os;
        os << "{\"dimension\":" << dr.dimension << ",\"colorings\":[";
        for (size_t c = 0; c < dr.colorings.size(); ++c) {
            if (c) os << ',';
            os << "{\"classes\":[";
            for (size_t k = 0; k < dr.colorings[c].classes.size(); ++k) {
                if (k) os << ',';
                os << '[';
                const auto& cls = dr.colorings[c].classes[k];
                for (size_t i = 0; i < cls.size(); ++i)
                    os << (i ? "," : "") << '[' << cls[i].x << ',' << cls[i].y << ']';
                os << ']';
            }
            os << "],\"realizer\":" << realizer_to_json(dr.colorings[c].realizer) << "}";
        }
        os << "]}";
        return os.str();
    } catch (const std::exception& e) {
        return std::string("{\"error\":\"") + e.what() + "\"}";
    }
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
    if (d.meta) {
        // parse_document guarantees execution and/or poset is present, so meta is
        // never first — always separate it with a comma.
        os << ",\"meta\":{";
        bool mfirst = true;
        auto comma = [&]{ if (!mfirst) os << ','; mfirst = false; };
        if (d.meta->notes)       { comma(); os << "\"notes\":\"" << *d.meta->notes << "\""; }
        if (d.meta->dimension)   { comma(); os << "\"dimension\":" << *d.meta->dimension; }
        if (d.meta->source_hash) { comma(); os << "\"source_hash\":\"" << *d.meta->source_hash << "\""; }
        if (d.meta->realizers) {
            comma(); os << "\"realizers\":[";
            for (size_t r = 0; r < d.meta->realizers->size(); ++r)
                os << (r ? "," : "") << realizer_to_json((*d.meta->realizers)[r]);
            os << ']';
        }
        os << '}';
    }
    os << '}';
    return os.str();
}

std::string dump_document_json(const std::string& doc_json) {
    YAML::Node n = YAML::Load(doc_json);
    Document d;
    if (n["poset"]) {
        Poset p; p.n_vertices = n["poset"]["n_vertices"].as<int>();
        p.edges.assign(p.n_vertices, {});
        const YAML::Node& edges = n["poset"]["edges"];
        for (int u = 0; u < (int)edges.size() && u < p.n_vertices; ++u)
            for (const auto& v : edges[u]) p.edges[u].push_back(v.as<int>());
        p.validate();
        d.poset = std::move(p);
    }
    if (n["meta"]) {
        Meta m;
        const YAML::Node& mn = n["meta"];
        if (mn["notes"])       m.notes = mn["notes"].as<std::string>();
        if (mn["dimension"])   m.dimension = mn["dimension"].as<int>();
        if (mn["source_hash"]) m.source_hash = mn["source_hash"].as<std::string>();
        if (mn["realizers"]) {
            std::vector<std::vector<std::vector<int>>> rs;
            for (const auto& r : mn["realizers"]) {
                std::vector<std::vector<int>> realizer;
                for (const auto& ext : r) {
                    std::vector<int> e;
                    for (const auto& v : ext) e.push_back(v.as<int>());
                    realizer.push_back(std::move(e));
                }
                rs.push_back(std::move(realizer));
            }
            m.realizers = std::move(rs);
        }
        d.meta = std::move(m);
    }
    return dump_document(d);
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
    emscripten::function("dimension", &dimension_json);
    emscripten::function("findOneRealizer", &find_one_realizer_json);
    emscripten::function("allRealizers", &all_realizers_json);
    emscripten::function("expandExecution", &expand_execution_json);
    emscripten::function("parseDocument", &parse_document_json);
    emscripten::function("dumpPoset", &dump_poset_json);
    emscripten::function("dumpExecution", &dump_execution_json);
    emscripten::function("dumpDocument", &dump_document_json);
    emscripten::function("version", &lib_version);
}
