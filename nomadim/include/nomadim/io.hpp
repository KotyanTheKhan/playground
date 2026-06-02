#ifndef NOMADIM_IO_HPP
#define NOMADIM_IO_HPP

#include "nomadim/execution.hpp"
#include "nomadim/poset.hpp"
#include <optional>
#include <string>
#include <vector>

namespace nomadim {

// Cached annotations carried alongside a document. `notes` is user-authored;
// `dimension`/`realizers` are computed results, valid only while `source_hash`
// matches the current poset (else they are stale and should be recomputed).
struct Meta {
    std::optional<std::string> notes;
    std::optional<int> dimension;
    std::optional<std::vector<std::vector<std::vector<int>>>> realizers; // [realizer][extension][vertex]
    std::optional<std::string> source_hash;
};

// A parsed YAML document: may contain an execution, a poset, or both, plus meta.
struct Document {
    std::optional<Execution> execution;
    std::optional<Poset> poset;
    std::optional<Meta> meta;
};

// Parse YAML text. Throws std::runtime_error on parse errors, on malformed
// sync/edge pairs (each must be a 2-element list), or if neither top-level key
// (`execution`/`poset`) is present. The contained values are validated.
Document parse_document(const std::string& text);

// Read and parse a file (throws std::runtime_error if it cannot be opened).
Document load_file(const std::string& path);

// Serialize to YAML text.
std::string dump_execution(const Execution& e);
std::string dump_poset(const Poset& p);

// Stable order-insensitive hash (hex) of a poset's adjacency, for meta staleness.
std::string poset_hash(const adjacency_list& edges);

// Serialize a whole document (execution + poset + meta), omitting absent parts.
std::string dump_document(const Document& d);

// Write text to a file (throws std::runtime_error if it cannot be opened).
void save_file(const std::string& path, const std::string& text);

} // namespace nomadim

#endif // NOMADIM_IO_HPP
