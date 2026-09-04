#ifndef AMAYA_INTERRUPT_H
#define AMAYA_INTERRUPT_H

#include <atomic>
#include <stdexcept>

/*
Every algorithm exposed to Python (pad closure, intersection, determinization, minimization,
the various `construct_nfa_from_*` state-graph explorations, ...) can run for an unbounded time
inside a single C++ call, without ever returning control to the Python interpreter. Python's own
SIGINT handling only takes effect once the interpreter's bytecode eval loop runs again, so Ctrl-C
(and SIGTERM, which Python does not auto-handle at all) is otherwise silently swallowed until the
C++ call happens to finish on its own.

The fix: a single process-wide flag, set by a signal handler installed only while we are inside
such a call (`Interrupt_Guard`), and polled from inside the long-running loops themselves
(`AMAYA_CHECK_INTERRUPT`). When set, the loop throws `Amaya_Interrupted`, which unwinds back
through Cython (every entry point is declared `except +` in base.pyx) as a Python `RuntimeError`
carrying the signal name; base.pyx re-raises it as `KeyboardInterrupt`/`SystemExit` as appropriate.
*/

extern std::atomic<bool> g_interrupt_requested;
extern std::atomic<int>  g_interrupt_signal;  // holds the raw signal number that fired

struct Amaya_Interrupted : public std::runtime_error {
    explicit Amaya_Interrupted(int signal_number);
};

#define AMAYA_CHECK_INTERRUPT() \
    do { if (g_interrupt_requested.load(std::memory_order_relaxed)) { \
        throw Amaya_Interrupted(g_interrupt_signal.load(std::memory_order_relaxed)); \
    } } while (0)

/*
RAII scope guard - installs SIGINT/SIGTERM handlers that just flip `g_interrupt_requested` for the
duration of a top-level algorithm call, and restores whatever handlers were previously in place
(Python's own SIGINT handler, in the common case) once the call returns or unwinds. Guards nest
(one algorithm calling into another that also constructs a guard) via a depth counter, so only the
outermost instance actually touches the process' signal handlers.
*/
struct Interrupt_Guard {
    Interrupt_Guard();
    ~Interrupt_Guard();
};

#endif
