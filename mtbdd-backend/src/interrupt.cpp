#include "../include/interrupt.hpp"

#include <csignal>
#include <string>

std::atomic<bool> g_interrupt_requested{false};
std::atomic<int>  g_interrupt_signal{0};

static const char* signal_name(int signal_number) {
    switch (signal_number) {
        case SIGINT:  return "SIGINT";
        case SIGTERM: return "SIGTERM";
        default:      return "signal";
    }
}

Amaya_Interrupted::Amaya_Interrupted(int signal_number)
    : std::runtime_error(std::string("amaya: interrupted by ") + signal_name(signal_number)) {}

namespace {
    // Async-signal-safe: touches only a lock-free atomic, nothing else.
    void amaya_signal_handler(int signal_number) {
        g_interrupt_signal.store(signal_number, std::memory_order_relaxed);
        g_interrupt_requested.store(true, std::memory_order_relaxed);
    }

    int guard_depth = 0;
    struct sigaction previous_sigint_action;
    struct sigaction previous_sigterm_action;
}

Interrupt_Guard::Interrupt_Guard() {
    if (guard_depth == 0) {
        struct sigaction action = {};
        action.sa_handler = amaya_signal_handler;
        sigemptyset(&action.sa_mask);
        action.sa_flags = 0;  // deliberately no SA_RESTART: interrupt blocking syscalls too

        sigaction(SIGINT, &action, &previous_sigint_action);
        sigaction(SIGTERM, &action, &previous_sigterm_action);

        g_interrupt_requested.store(false, std::memory_order_relaxed);
    }
    guard_depth++;
}

Interrupt_Guard::~Interrupt_Guard() {
    guard_depth--;
    if (guard_depth == 0) {
        sigaction(SIGINT, &previous_sigint_action, nullptr);
        sigaction(SIGTERM, &previous_sigterm_action, nullptr);
        g_interrupt_requested.store(false, std::memory_order_relaxed);
    }
}
