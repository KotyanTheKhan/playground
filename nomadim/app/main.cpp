#include "cmd_check.hpp"
#include "cmd_enumerate.hpp"
#include "cmd_convert.hpp"
#include "nomadim/types.hpp"
#include <CLI/CLI.hpp>
#include <thread>
#include <iostream>

int main(int argc, char** argv) {
    CLI::App app{"nomadim: poset dimension-2 tooling"};
    app.set_version_flag("--version", std::string(nomadim::version()));
    app.require_subcommand(1);

    std::string check_path;
    auto* check = app.add_subcommand("check", "Report whether a poset/execution has dimension <= 2");
    check->add_option("file", check_path, "YAML poset/execution file")->required();

    int n_procs = 0, max_sync = -1;
    unsigned threads = std::thread::hardware_concurrency();
    std::string enum_out;
    auto* en = app.add_subcommand("enumerate", "Enumerate non-isomorphic dim-2 executions");
    en->add_option("-n,--procs", n_procs, "Number of processes")->required();
    en->add_option("-k,--max-sync", max_sync, "Max synchronizations (default: 2*n_procs)");
    en->add_option("-j,--threads", threads, "Worker threads (>=1)")->check(CLI::PositiveNumber);
    en->add_option("-o,--out", enum_out, "Write found executions to this YAML file");

    std::string conv_in, conv_out;
    auto* conv = app.add_subcommand("convert", "Expand an execution into a poset document");
    conv->add_option("input", conv_in, "Input execution YAML")->required();
    conv->add_option("output", conv_out, "Output poset YAML")->required();

    CLI11_PARSE(app, argc, argv);

    try {
        if (*check)  return nomadim::cmd_check(check_path);
        if (*en) {
            if (max_sync < 0) max_sync = 2 * n_procs;
            return nomadim::cmd_enumerate(n_procs, max_sync, threads, enum_out);
        }
        if (*conv)   return nomadim::cmd_convert(conv_in, conv_out);
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
