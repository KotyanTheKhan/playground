#include "nomadim/io.hpp"
#include <yaml-cpp/yaml.h>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <cstdint>
#include <set>

namespace nomadim {

namespace {
std::pair<int,int> read_pair(const YAML::Node& n, const char* what) {
    if (!n.IsSequence() || n.size() != 2)
        throw std::runtime_error(std::string(what) + " must be a 2-element list");
    return {n[0].as<int>(), n[1].as<int>()};
}
} // namespace

Document parse_document(const std::string& text) {
    YAML::Node root;
    try {
        root = YAML::Load(text);
    } catch (const YAML::Exception& e) {
        throw std::runtime_error(std::string("YAML parse error: ") + e.what());
    }
    if (!root || !root.IsMap())
        throw std::runtime_error("document must be a YAML mapping");

    Document doc;
    if (root["execution"]) {
        const YAML::Node& en = root["execution"];
        Execution e;
        e.n_procs = en["n_procs"].as<int>();
        if (en["syncs"])
            for (const auto& s : en["syncs"]) e.syncs.push_back(read_pair(s, "sync"));
        e.validate();
        doc.execution = std::move(e);
    }
    if (root["poset"]) {
        const YAML::Node& pn = root["poset"];
        Poset p;
        p.n_vertices = pn["n_vertices"].as<int>();
        p.edges.assign(p.n_vertices, {});
        if (pn["edges"])
            for (const auto& edge : pn["edges"]) {
                auto uv = read_pair(edge, "edge");
                if (uv.first < 0 || uv.first >= p.n_vertices)
                    throw std::runtime_error("edge source out of range");
                p.edges[uv.first].push_back(uv.second);
            }
        p.validate();
        doc.poset = std::move(p);
    }
    if (root["meta"]) {
        const YAML::Node& mn = root["meta"];
        Meta meta;
        if (mn["notes"])       meta.notes = mn["notes"].as<std::string>();
        if (mn["dimension"])   meta.dimension = mn["dimension"].as<int>();
        if (mn["source_hash"]) meta.source_hash = mn["source_hash"].as<std::string>();
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
            meta.realizers = std::move(rs);
        }
        doc.meta = std::move(meta);
    }
    if (!doc.execution && !doc.poset)
        throw std::runtime_error("document must contain an 'execution' or 'poset' key");
    return doc;
}

Document load_file(const std::string& path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open file: " + path);
    std::stringstream ss; ss << in.rdbuf();
    return parse_document(ss.str());
}

std::string dump_execution(const Execution& e) {
    YAML::Emitter out;
    out << YAML::BeginMap << YAML::Key << "execution" << YAML::Value << YAML::BeginMap;
    out << YAML::Key << "n_procs" << YAML::Value << e.n_procs;
    out << YAML::Key << "syncs" << YAML::Value << YAML::BeginSeq;
    for (auto const& s : e.syncs) {
        out << YAML::Flow << YAML::BeginSeq << s.first << s.second << YAML::EndSeq;
    }
    out << YAML::EndSeq << YAML::EndMap << YAML::EndMap;
    return out.c_str();
}

std::string dump_poset(const Poset& p) {
    YAML::Emitter out;
    out << YAML::BeginMap << YAML::Key << "poset" << YAML::Value << YAML::BeginMap;
    out << YAML::Key << "n_vertices" << YAML::Value << p.n_vertices;
    out << YAML::Key << "edges" << YAML::Value << YAML::BeginSeq;
    for (int u = 0; u < p.n_vertices; ++u)
        for (int v : p.edges[u])
            out << YAML::Flow << YAML::BeginSeq << u << v << YAML::EndSeq;
    out << YAML::EndSeq << YAML::EndMap << YAML::EndMap;
    return out.c_str();
}

std::string poset_hash(const adjacency_list& edges) {
    // FNV-1a over a canonical "u>v;" edge list (each adjacency sorted), so the
    // hash depends only on the relation, not on edge ordering.
    uint64_t h = 1469598103934665603ULL;
    auto mix = [&](uint64_t x) {
        for (int b = 0; b < 8; ++b) { h ^= (x & 0xff); h *= 1099511628211ULL; x >>= 8; }
    };
    for (int u = 0; u < (int)edges.size(); ++u) {
        std::set<int> sorted(edges[u].begin(), edges[u].end());
        for (int v : sorted) { mix((uint64_t)u); mix((uint64_t)v); mix('|'); }
    }
    static const char* hex = "0123456789abcdef";
    std::string out;
    for (int s = 60; s >= 0; s -= 4) out.push_back(hex[(h >> s) & 0xf]);
    return out;
}

static void emit_meta(YAML::Emitter& out, const Meta& m) {
    out << YAML::Key << "meta" << YAML::Value << YAML::BeginMap;
    if (m.notes)       out << YAML::Key << "notes" << YAML::Value << *m.notes;
    if (m.dimension)   out << YAML::Key << "dimension" << YAML::Value << *m.dimension;
    if (m.source_hash) out << YAML::Key << "source_hash" << YAML::Value << *m.source_hash;
    if (m.realizers) {
        out << YAML::Key << "realizers" << YAML::Value << YAML::BeginSeq;
        for (const auto& realizer : *m.realizers) {
            out << YAML::BeginSeq;
            for (const auto& ext : realizer) {
                out << YAML::Flow << YAML::BeginSeq;
                for (int v : ext) out << v;
                out << YAML::EndSeq;
            }
            out << YAML::EndSeq;
        }
        out << YAML::EndSeq;
    }
    out << YAML::EndMap;
}

std::string dump_document(const Document& d) {
    YAML::Emitter out;
    out << YAML::BeginMap;
    if (d.execution) {
        out << YAML::Key << "execution" << YAML::Value << YAML::BeginMap;
        out << YAML::Key << "n_procs" << YAML::Value << d.execution->n_procs;
        out << YAML::Key << "syncs" << YAML::Value << YAML::BeginSeq;
        for (auto const& s : d.execution->syncs)
            out << YAML::Flow << YAML::BeginSeq << s.first << s.second << YAML::EndSeq;
        out << YAML::EndSeq << YAML::EndMap;
    }
    if (d.poset) {
        out << YAML::Key << "poset" << YAML::Value << YAML::BeginMap;
        out << YAML::Key << "n_vertices" << YAML::Value << d.poset->n_vertices;
        out << YAML::Key << "edges" << YAML::Value << YAML::BeginSeq;
        for (int u = 0; u < d.poset->n_vertices; ++u)
            for (int v : d.poset->edges[u])
                out << YAML::Flow << YAML::BeginSeq << u << v << YAML::EndSeq;
        out << YAML::EndSeq << YAML::EndMap;
    }
    if (d.meta) emit_meta(out, *d.meta);
    out << YAML::EndMap;
    return out.c_str();
}

void save_file(const std::string& path, const std::string& text) {
    std::ofstream o(path);
    if (!o) throw std::runtime_error("cannot open file for writing: " + path);
    o << text;
}

} // namespace nomadim
