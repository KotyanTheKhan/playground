#ifndef NOMADIM_CMD_ENUMERATE_HPP
#define NOMADIM_CMD_ENUMERATE_HPP
#include <string>
namespace nomadim {
int cmd_enumerate(int n_procs, int max_sync, unsigned threads, const std::string& out_path,
                  bool all_dims = false, bool with_dim = false, int max_vertices = 64,
                  int max_cpairs = 64);
}
#endif
