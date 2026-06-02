#include "cmd_convert.hpp"
#include "nomadim/io.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/poset.hpp"
#include <iostream>

namespace nomadim {

int cmd_convert(const std::string& in, const std::string& out) {
    Document d = load_file(in);
    if (!d.execution) {
        std::cerr << "convert expects an 'execution' document\n";
        return 1;
    }
    ProcessGraph g = ProcessGraph::build(*d.execution);
    Poset p = Poset::from(g);
    save_file(out, dump_poset(p));
    std::cout << "Wrote expanded poset (" << p.n_vertices << " vertices) to " << out << "\n";
    return 0;
}

} // namespace nomadim
