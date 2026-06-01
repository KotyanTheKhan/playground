#include <benchmark/benchmark.h>

#include "nomadim/enumerate.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/types.hpp"

#include <thread>
#include <algorithm>

using namespace nomadim;

static adjacency_list canonical_graph() {
    return ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}}).graph;
}

static adjacency_list s3_graph() {
    adjacency_list s3(6);
    s3[0] = {4, 5};
    s3[1] = {3, 5};
    s3[2] = {3, 4};
    return s3;
}

// --- Micro: is_dim2 (stable, auto-iterated) ---

static void dim2_canonical(benchmark::State& state) {
    adjacency_list g = canonical_graph();
    for (auto _ : state) {
        bool r = is_dim2(g);
        benchmark::DoNotOptimize(r);
    }
}
BENCHMARK(dim2_canonical);

static void dim2_s3(benchmark::State& state) {
    adjacency_list g = s3_graph();
    for (auto _ : state) {
        bool r = is_dim2(g);
        benchmark::DoNotOptimize(r);
    }
}
BENCHMARK(dim2_s3);

// --- Macro: enumerate (one run per measurement; median from --benchmark_repetitions) ---

static void run_enum(benchmark::State& state, int n, int k, unsigned j, int expected) {
    for (auto _ : state) {
        EnumerateResult r = enumerate(n, k, j);
        benchmark::DoNotOptimize(r.count);
        if (r.count != expected)
            state.SkipWithError("unexpected enumerate count");
    }
}

static void enumerate_4_6_j1(benchmark::State& s) { run_enum(s, 4, 6, 1, 102); }
BENCHMARK(enumerate_4_6_j1)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

static void enumerate_4_7_j1(benchmark::State& s) { run_enum(s, 4, 7, 1, 634); }
BENCHMARK(enumerate_4_7_j1)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

static void enumerate_5_7_j1(benchmark::State& s) { run_enum(s, 5, 7, 1, 40); }
BENCHMARK(enumerate_5_7_j1)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

static void enumerate_4_7_par(benchmark::State& s) {
    unsigned j = std::max(2u, std::thread::hardware_concurrency());
    run_enum(s, 4, 7, j, 634);
}
BENCHMARK(enumerate_4_7_par)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

BENCHMARK_MAIN();
