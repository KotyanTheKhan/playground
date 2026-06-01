#ifndef NOMADIM_ISOMORPHISM_HPP
#define NOMADIM_ISOMORPHISM_HPP

#include "nomadim/process_graph.hpp"
#include <vector>

namespace nomadim {

// True if the two process graphs are isomorphic under a process permutation.
bool is_isomorphic(const ProcessGraph& l, const ProcessGraph& r);

// All process graphs obtained by permuting the process labels of `pg`'s syncs.
std::vector<ProcessGraph> generate_all_isomorphic(const ProcessGraph& pg);

// Canonical (sorted) per-process synchronization signature, used as a cache key.
ProcessGraph::PEHash canonical_sync_name(const ProcessGraph& pg);

} // namespace nomadim

#endif // NOMADIM_ISOMORPHISM_HPP
