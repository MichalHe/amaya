import argparse
import matplotlib.pyplot as plt
import numpy as np
import math
from typing import (
    Dict,
    Tuple,
)


DATA = {
    'x': np.array([1, 2, 3, 4, 100, 13]),
    'y': np.array([1, 2, 3, 4, 12, 65]),
}

PLOT_STUFF = ('x', 'y')


def draw_single_plot(solver_pair: Tuple[str, str], data: Dict[str, np.array], target_axis, limits=None):
    x_solver_data = data[solver_pair[0]]
    y_solver_data = data[solver_pair[1]]
    
    target_axis.scatter(x_solver_data, y_solver_data, marker='x')
    
    def calc_limit(bound_val, margin_growth_fun, margin_rounding_fun):
        log = math.log10(bound_val)
        rounded_log = margin_rounding_fun(log)
        if abs(log - rounded_log) < 0.05:
            rounded_log = margin_growth_fun(rounded_log)
        limit = math.pow(10, rounded_log)
        return limit
    
    if not limits:
        lower_limit = min(np.min(x_solver_data), np.min(y_solver_data))
        lower_limit = calc_limit(lower_limit, lambda margin_log: margin_log - 1, math.floor)
        upper_limit = max(np.max(x_solver_data), np.min(y_solver_data))
        upper_limit = calc_limit(upper_limit, lambda margin_log: margin_log + 1, math.ceil)

        limits = (lower_limit, upper_limit)
        
    target_axis.set_xlim(limits)
    target_axis.set_ylim(limits)
    target_axis.set_xscale('log')
    target_axis.set_yscale('log')
    
    lower_limit, upper_limit = limits
    current_line_pos = lower_limit * 10
    for i in range(round(math.log10(lower_limit)), round(math.log10(upper_limit))):
        target_axis.hlines(current_line_pos, limits[0], limits[1], color='gray', linewidth=0.3, linestyle='dotted')
        target_axis.vlines(current_line_pos, limits[0], limits[1], color='gray', linewidth=0.3, linestyle='dotted')
        current_line_pos *= 10
    target_axis.plot(np.array(limits), np.array(limits), color='gray', linewidth=0.5, linestyle='dashed')
    target_axis.set_aspect(1.0)

    target_axis.set_xlabel(solver_pair[0])
    target_axis.set_ylabel(solver_pair[1])


fig, ax = plt.subplots(1)

draw_single_plot(PLOT_STUFF, DATA, ax)
plt.show()
