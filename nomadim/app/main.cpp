#include "cmd_check.hpp"
#include "cmd_enumerate.hpp"
#include "cmd_convert.hpp"
#include "cmd_dimension.hpp"
#include "nomadim/types.hpp"
#include <CLI/CLI.hpp>
#include <thread>
#include <iostream>

int main(int argc, char** argv) {
    CLI::App app{"nomadim: poset order-dimension tooling"};
    app.set_version_flag("--version", std::string(nomadim::version()));
    app.require_subcommand(1);

    std::string check_path;
    auto* check = app.add_subcommand("check", "Report whether a poset/execution has dimension <= 2");
    check->add_option("file", check_path, "YAML poset/execution file")->required();

    int n_procs = 0, max_sync = -1;
    unsigned threads = std::thread::hardware_concurrency();
    std::string enum_out;
    bool enum_all_dims = false;
    auto* en = app.add_subcommand("enumerate", "Enumerate non-isomorphic fully-synchronized executions");
    en->add_option("-n,--procs", n_procs, "Number of processes")->required()->check(CLI::PositiveNumber);
    en->add_option("-k,--max-sync", max_sync, "Max synchronizations (default: 2*n_procs)");
    en->add_option("-j,--threads", threads, "Worker threads (>=1)")->check(CLI::PositiveNumber);
    en->add_option("-o,--out", enum_out, "Write found executions to this YAML file");
    en->add_flag("--all-dims", enum_all_dims, "Keep executions of every dimension (not just dim<=2)");
    bool enum_with_dim = false;
    int enum_max_vertices = 64, enum_max_cpairs = 64;
    en->add_flag("--with-dim", enum_with_dim, "Compute each shape's dimension; print histogram, write meta");
    en->add_option("--max-vertices", enum_max_vertices, "Vertex cap for --with-dim (default 64)");
    en->add_option("--max-cpairs", enum_max_cpairs, "Critical-pair cap for --with-dim (default 64)");

    std::string conv_in, conv_out;
    auto* conv = app.add_subcommand("convert", "Expand an execution into a poset document");
    conv->add_option("input", conv_in, "Input execution YAML")->required();
    conv->add_option("output", conv_out, "Output poset YAML")->required();

    std::string dim_path, dim_out;
    bool dim_realizers = false, dim_all = false, dim_quick = false;
    int dim_max_vertices = 16, dim_max_cpairs = 64;
    auto* dim = app.add_subcommand("dimension", "Report order dimension (any >= 1), with optional realizers");
    dim->add_option("file", dim_path, "YAML poset/execution file")->required();
    dim->add_flag("--realizers", dim_realizers, "Print one realizer");
    dim->add_flag("--all", dim_all, "Print all minimum colorings + realizers");
    dim->add_flag("--quick", dim_quick, "Dimension only; skip realizer/coloring enumeration (fast)");
    int dim_le = 0;
    dim->add_option("--le", dim_le, "Test only whether dimension <= this K (cheap when yes); exit 0=yes,2=no");
    dim->add_option("--max-vertices", dim_max_vertices, "Vertex cap (default 16)");
    dim->add_option("--max-cpairs", dim_max_cpairs, "Critical-pair cap (default 64)");
    dim->add_option("-o,--out", dim_out, "Write document with computed meta to this file");

    CLI11_PARSE(app, argc, argv);

    try {
        if (*check)  return nomadim::cmd_check(check_path);
        if (*en) {
            if (max_sync < 0) max_sync = 2 * n_procs;
            return nomadim::cmd_enumerate(n_procs, max_sync, threads, enum_out, enum_all_dims,
                                          enum_with_dim, enum_max_vertices, enum_max_cpairs);
        }
        if (*conv)   return nomadim::cmd_convert(conv_in, conv_out);
        if (*dim)
            return nomadim::cmd_dimension(dim_path, dim_realizers, dim_all,
                                          dim_max_vertices, dim_out, dim_quick, dim_max_cpairs,
                                          dim_le);
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
