#include "nomadim/process_graph.hpp"
#include <cassert>

namespace nomadim {

void ProcessGraph::init(int process_num) {
    graph.clear();
    proc_num = process_num;
    proc_last_vertex.clear();
    next_vertex = 0;
    labels.clear();
    proc_verteces.clear();

    proc_last_vertex.resize(proc_num);
    proc_verteces.resize(proc_num);

    for (int i = 0; i < proc_num; ++i) {
        int cur_vert = next_vertex++;
        graph.push_back({});
        proc_last_vertex[i] = cur_vert;
        labels.push_back({i, 0});
        proc_verteces[i].push_back(cur_vert);
    }

    network.clear();
    network.resize(proc_num);
    proc_sync_name.clear();
    proc_sync_name.resize(proc_num);
}

void ProcessGraph::sync(int proc1, int proc2) {
    assert(proc1 >= 0 && proc1 < proc_num);
    assert(proc2 >= 0 && proc2 < proc_num);

    syncs.emplace_back(proc1, proc2);

    int p1 = proc_last_vertex[proc1];
    int p2 = proc_last_vertex[proc2];

    int new_vertex = next_vertex++;  graph.push_back({});
    int p1nv = next_vertex++;        graph.push_back({});
    int p2nv = next_vertex++;        graph.push_back({});

    graph[p1].push_back(new_vertex);
    graph[p2].push_back(new_vertex);
    graph[new_vertex].push_back(p1nv);
    graph[new_vertex].push_back(p2nv);

    proc_last_vertex[proc1] = p1nv;
    proc_last_vertex[proc2] = p2nv;
    proc_verteces[proc1].push_back(p1nv);
    proc_verteces[proc2].push_back(p2nv);

    labels.push_back({-1, -1});
    labels.push_back({proc1, labels[p1].num + 1});
    labels.push_back({proc2, labels[p2].num + 1});

    network[proc1].insert(proc2);
    network[proc2].insert(proc1);

    char sync_num = (char)(syncs.size() - 1) + '0';
    proc_sync_name[proc1] += sync_num;
    proc_sync_name[proc2] += sync_num;
}

ProcessGraph ProcessGraph::build(const Execution& e) {
    ProcessGraph g;
    g.init(e.n_procs);
    for (auto const& s : e.syncs) g.sync(s.first, s.second);
    return g;
}

} // namespace nomadim
