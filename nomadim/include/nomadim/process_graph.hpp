#ifndef NOMADIM_PROCESS_GRAPH_HPP
#define NOMADIM_PROCESS_GRAPH_HPP

#include "nomadim/types.hpp"
#include "nomadim/execution.hpp"
#include <vector>
#include <string>
#include <unordered_set>
#include <utility>

namespace nomadim {

struct Label {
    int proc;
    int num;
};

// Event-structure DAG built from an execution. Each process is a chain of event
// vertices; each sync inserts a meet vertex joining the current last vertices of
// two processes and spawns two new last vertices.
class ProcessGraph {
public:
    int proc_num = 0;

    adjacency_list graph;                       // DAG adjacency (event -> successors)
    std::vector<int> proc_last_vertex;
    int next_vertex = 0;

    std::vector<std::unordered_set<int>> network;   // process-level sync adjacency
    std::vector<Label> labels;
    std::vector<std::vector<int>> proc_verteces;
    std::vector<std::pair<int,int>> syncs;

    using PEHash = std::vector<std::string>;
    PEHash proc_sync_name;                      // per-process synchronization signature

    void init(int process_num);
    void sync(int proc1, int proc2);

    // Convenience: init(e.n_procs) then replay e.syncs.
    static ProcessGraph build(const Execution& e);

private:
    int add_vertex_to_proc(int proc);
};

} // namespace nomadim

#endif // NOMADIM_PROCESS_GRAPH_HPP
