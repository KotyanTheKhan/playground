#ifndef NOMADIM_IO_HPP
#define NOMADIM_IO_HPP

#include "nomadim/execution.hpp"
#include "nomadim/poset.hpp"
#include <optional>
#include <string>

namespace nomadim {

// A parsed YAML document: may contain an execution, a poset, or both.
struct Document {
    std::optional<Execution> execution;
    std::optional<Poset> poset;
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

// Write text to a file (throws std::runtime_error if it cannot be opened).
void save_file(const std::string& path, const std::string& text);

} // namespace nomadim

#endif // NOMADIM_IO_HPP
