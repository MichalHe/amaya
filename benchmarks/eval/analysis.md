---
jupyter:
  jupytext:
    text_representation:
      extension: .md
      format_name: markdown
      format_version: '1.2'
      jupytext_version: 1.5.2
  kernelspec:
    display_name: PyCharm (eval)
    language: python
    name: pycharm-1b520b84
---

# Analysis of results of SMT solvers

We start with some auxiliary functions.

```python
# PREAMBLE
import datetime
import pandas as pd
import re as re
import tabulate as tab
import plotnine as p9
import math
import mizani.formatters as mizani
from IPython.display import HTML, display


# in seconds
TIMEOUT = 300
TIMEOUT_VAL = TIMEOUT * 1.1
TIME_MIN = 0.01

# For reading in files
def read_file(filename):
    """Reads a CSV file into Panda's data frame"""
    df_loc = pd.read_csv(
        filename,
        sep=";",
        comment="#",
        na_values=['ERR', 'TO', 'MISSING'])
    return df_loc


# For printing scatter plots
def scatter_plot(df, xcol, ycol, domain, xname=None, yname=None, log=False, width=6, height=6, clamp=True, tickCount=5):
    assert len(domain) == 2

    POINT_SIZE = 1.0
    DASH_PATTERN = (0, (6, 2))

    if xname is None:
        xname = xcol
    if yname is None:
        yname = ycol

    # formatter for axes' labels
    ax_formatter = mizani.custom_format('{:n}')

    if clamp:  # clamp overflowing values if required
        df = df.copy(deep=True)
        df.loc[df[xcol] > domain[1], xcol] = domain[1]
        df.loc[df[ycol] > domain[1], ycol] = domain[1]

    # generate scatter plot
    scatter = p9.ggplot(df)
    scatter += p9.aes(x=xcol, y=ycol)
    scatter += p9.geom_point(size=POINT_SIZE, na_rm=True)
    scatter += p9.labs(x=xname, y=yname)

    # rug plots
    scatter += p9.geom_rug(na_rm=True, sides="tr", alpha=0.05)

    if log:  # log scale
        scatter += p9.scale_x_log10(limits=domain, labels=ax_formatter)
        scatter += p9.scale_y_log10(limits=domain, labels=ax_formatter)
    else:
        scatter += p9.scale_x_continuous(limits=domain, labels=ax_formatter)
        scatter += p9.scale_y_continuous(limits=domain, labels=ax_formatter)

    # scatter += p9.theme_xkcd()
    scatter += p9.theme_bw()
    scatter += p9.theme(panel_grid_major=p9.element_line(color='#666666', alpha=0.5))
    scatter += p9.theme(panel_grid_minor=p9.element_blank())
    scatter += p9.theme(figure_size=(width, height))
    scatter += p9.theme(text=p9.element_text(size=24, color="black"))

    # generate additional lines
    scatter += p9.geom_abline(intercept=0, slope=1, linetype=DASH_PATTERN)  # diagonal
    scatter += p9.geom_vline(xintercept=domain[1], linetype=DASH_PATTERN)  # vertical rule
    scatter += p9.geom_hline(yintercept=domain[1], linetype=DASH_PATTERN)  # horizontal rule

    res = scatter

    return res


# Print a matrix of plots
def matrix_plot(list_of_plots, cols):
    assert len(list_of_plots) > 0
    assert cols >= 0

    matrix_plot = None
    row = None
    for i in range(0, len(list_of_plots)):
        if i % cols == 0:  # starting a new row
            row = list_of_plots[i]
        else:
            row |= list_of_plots[i]

        if (i + 1) % cols == 0 or i + 1 == len(list_of_plots):  # last chart in a row
            if not matrix_plot:  # first row finished
                matrix_plot = row
            else:
                matrix_plot &= row

    return matrix_plot


# table to LaTeX file
def table_to_file(table, headers, out_file):
    with open(f"plots/{out_file}.tex", mode='w') as fl:
        print(tab.tabulate(table, headers=headers, tablefmt="latex"), file=fl)
```

Let us now write the function that is given an input CSV with results of
a benchmark and it analyses it.

```python
# generate evaluation
def gen_evaluation(file_input):
    df = read_file(file_input)

    print(f"file:  {file_input}")
    print(f"time:  {datetime.datetime.now()}")
    print(f"# of formulae: {len(df)}")

    # trim strings in the data frame
    df = df.applymap(lambda x: x.strip() if isinstance(x, str) else x)

    # interpret anything that is not SAT/UNSAT as TIMEOUT
    for i in ["z3", "cvc4"]:
      #df.loc[(df[i + "-result"] != "sat"), i + "-runtime"] = None
      df.loc[(df[i + "-result"] != "sat") & (df[i + "-result"] != "unsat"), i + "-runtime"] = None

    summary_times = dict()
    for col in df.columns:
        if re.search('-runtime$', col):
            summary_times[col] = dict()
            summary_times[col]['max'] = df[col].max()
            summary_times[col]['min'] = df[col].min()
            summary_times[col]['mean'] = df[col].mean()
            summary_times[col]['median'] = df[col].median()
            summary_times[col]['std'] = df[col].std()
            summary_times[col]['timeouts'] = df[col].isna().sum()

    df_summary_times = pd.DataFrame(summary_times).transpose()



    tab_interesting = []
    for i in ["z3", "cvc4"]:
        row = df_summary_times.loc[i + '-runtime']
        row_dict = dict(row)
        row_dict.update({'name': i})
        tab_interesting.append([row_dict['name'],
                                # row_dict['min'],
                                row_dict['max'],
                                row_dict['mean'],
                                row_dict['median'],
                                row_dict['std'],
                                row_dict['timeouts']])

    # headers = ["name", "min", "max", "mean", "median", "std. dev", "timeouts"]
    headers = ["method", "max", "mean", "median", "std. dev", "timeouts"]
    print("######################################################################")
    print("####                            Table 1                           ####")
    print("######################################################################")
    print(tab.tabulate(tab_interesting, headers=headers, tablefmt="github"))
    #table_to_file(tab_interesting, headers, out_prefix + "_table1left")
    print("\n\n")

    # sanitizing NAs
    for col in df.columns:
        if re.search('-runtime$', col):
            df[col].fillna(TIMEOUT_VAL, inplace=True)
            df.loc[df[col] < TIME_MIN, col] = TIME_MIN  # to remove 0 (in case of log graph)
    display(df)


    # comparing wins/loses
    compare_methods = [("z3-runtime", "cvc4-runtime"),
                      ]

    tab_wins = []
    for left, right in compare_methods:
        left_over_right = df[df[left] < df[right]]
        right_timeouts = left_over_right[left_over_right[right] == TIMEOUT_VAL]

        right_over_left = df[df[left] > df[right]]
        left_timeouts = right_over_left[right_over_left[left] == TIMEOUT_VAL]

        tab_wins.append([right, len(left_over_right), len(right_timeouts), len(right_over_left), len(left_timeouts)])

    headers_wins = ["method", "wins", "wins-timeouts", "loses", "loses-timeouts"]
    print("######################################################################")
    print("####                             Table 2                          ####")
    print("######################################################################")
    print(tab.tabulate(tab_wins, headers=headers_wins, tablefmt="github"))
    #table_to_file(tab_wins, headers_wins, out_prefix + "_table1right")
    print("\n\n")

    print("##############    other claimed results    ###############")

    ############# the best solution ##########
    df['other_min-runtime'] = df[
        ['cvc4-runtime',]].min(axis=1)

    #ranker_best = df[df['ranker-maxr-autfilt-States'] < df['other_min-States']]
    #ranker_not_best = df[df['ranker-maxr-autfilt-States'] > df['other_min-States']]

    #num_ranker_not_strictly_best = len(df) - len(ranker_not_best)
    #num_ranker_not_strictly_best_percent = "{:.1f}".format(num_ranker_not_strictly_best / len(df) * 100)
    #num_ranker_strictly_best = len(ranker_best)
    #num_ranker_strictly_best_percent = "{:.1f}".format(num_ranker_strictly_best / len(df) * 100)
    #print(f"ranker non-strictly best: {num_ranker_not_strictly_best} (= {num_ranker_not_strictly_best_percent} %)")
    #print(f"ranker strictly best: {num_ranker_strictly_best} (= {num_ranker_strictly_best_percent} %)")
    # print(f"ranker not best = {len(ranker_not_best)}")

    to_cmp2 = [{'x': "z3", 'y': "cvc4",
                'xname': 'Z3', 'yname': 'CVC4',
                'max': TIMEOUT_VAL, 'tickCount': 3},
              ]

    # add fields where not present
    for params in to_cmp2:
        if 'xname' not in params:
            params['xname'] = None
        if 'yname' not in params:
            params['yname'] = None
        if 'max' not in params:
            params['max'] = TIMEOUT_VAL
        if 'tickCount' not in params:
            params['tickCount'] = 5
        if 'filename' not in params:
            params['filename'] = "fig_" + params['x'] + "_vs_" + params['y']

    size = 8
    plot_list = [(params['x'],
                  params['y'],
                  params['filename'],
                  scatter_plot(df,
                               xcol=params['x'] + '-runtime',
                               ycol=params['y'] + '-runtime',
                               xname=params['xname'], yname=params['yname'],
                               domain=[TIME_MIN, params['max']],
                               tickCount=params['tickCount'],
                               log=True, width=size, height=size)) for params
                 in to_cmp2]

    print("\n\n")
    print("Generating plots...")
    for x, y, filename, plot in plot_list:
        #filename = f"plots/{out_prefix}_{filename}.pdf"
        print(f"plotting x: {x}, y: {y}... saving to {filename}")
        # plot.save(filename, scale_factor=2)
        plot.save(filename=filename, dpi=1000)
        print(plot)

    # return benchmarks solvable only by 'engine'
    def only_solves(df, engine):
        # select those where engine finishes
        res = df[df[engine + '-runtime'] != TIMEOUT_VAL]
        for col in res.columns:
            if re.search('-runtime$', col) and not re.search(engine, col):
                res = res[res[col] == TIMEOUT_VAL]

        return res


    engines = ["z3",
               "cvc4",
              ]

    for i in engines:
        i_only_solves = only_solves(df, i)
        print(f"only {i} = " + str(len(i_only_solves)))
        if len(i_only_solves) > 0:
            print()
            print(tab.tabulate(i_only_solves, headers='keys'))
            print()

    def none_solves(df):
        # select those where engine finishes
        res = df
        for col in res.columns:
            if re.search('-runtime$', col):
                res = res[res[col] == TIMEOUT_VAL]

        return res

    unsolvable = none_solves(df)
    print("unsolvable: " + str(len(unsolvable)))
    print(tab.tabulate(unsolvable, headers='keys'))
    print("\n\n\n\n\n")

```

# UltimateAutomizer

```python
gen_evaluation("../results/2021-05-27-test/UltimateAutomizer.csv")
```

# Psyco

```python
gen_evaluation("../results/2021-05-27-test/tptp.csv")
```

# TPTP

```python
gen_evaluation("../results/2021-05-27-test/psyco.csv")
```

# 20190429-UltimateAutomizerSvcomp2019

```python
gen_evaluation("../results/2021-05-27-test/20190429-UltimateAutomizerSvcomp2019.csv")
```
