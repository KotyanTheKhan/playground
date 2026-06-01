#include "nomadim/io.hpp"
#include <yaml-cpp/yaml.h>
#include <fstream>
#include <sstream>
#include <stdexcept>

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

void save_file(const std::string& path, const std::string& text) {
    std::ofstream o(path);
    if (!o) throw std::runtime_error("cannot open file for writing: " + path);
    o << text;
}

} // namespace nomadim
