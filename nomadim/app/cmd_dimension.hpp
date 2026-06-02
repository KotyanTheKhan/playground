#ifndef NOMADIM_CMD_DIMENSION_HPP
#define NOMADIM_CMD_DIMENSION_HPP

#include <string>

namespace nomadim {

// `nomadim dimension <file>`: report order dimension. With show_realizers, print
// one realizer; with show_all, print every minimum coloring + realizer. If
// out_path is non-empty, write the document with meta (dimension, realizers,
// source_hash) filled in, preserving any existing notes.
int cmd_dimension(const std::string& path, bool show_realizers, bool show_all,
                  int max_vertices, const std::string& out_path);

} // namespace nomadim

#endif // NOMADIM_CMD_DIMENSION_HPP
