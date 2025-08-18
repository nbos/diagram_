import sys
import os
import csv
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import LogLocator, FuncFormatter

def read_columns(csv_path, x_col=0, y_col=1):
    xs, ys = [], []
    with open(csv_path, "r", newline="", errors="ignore") as f:
        reader = csv.reader(f)
        for row in reader:
            if len(row) <= max(x_col, y_col):
                continue
            try:
                x = float(row[x_col])
                y = float(row[y_col])
                xs.append(x)
                ys.append(y)
            except ValueError:
                continue
    return xs, ys

def sci_notation_formatter(x, pos):
    """Format numbers as 1e3, 2e3, ... (no +, no leading zeros)."""
    if x == 0:
        return "0"
    exp_str = f"{x:.0e}"  # e.g. "4e+02"
    coeff, exp = exp_str.split("e")
    coeff = str(int(float(coeff)))  # strip decimals
    exp = int(exp)  # convert to int, so +02 -> 2, -03 -> -3
    return f"{coeff}e{exp}"

def decimal_notation_formatter(x, pos):
    """Format log ticks using plain decimal notation (e.g. 9e3 -> 9000)."""
    if x == 0:
        return "0"
    # if x is an integer, print without decimals
    if abs(x - int(x)) < 1e-8:
        return str(int(x))
    else:
        # if it's not an exact integer, show as decimal
        return f"{x:.4g}"  # four significant figures


def main(csv_files):
    plt.figure(figsize=(6, 4))

    line_styles = [
        'k-', 'k--', 'k:', 'k-.',
        (0, (5, 1)), (0, (3, 5, 1, 5)),
        (0, (3, 1, 1, 1)), (0, (1, 1)), (0, (5, 10))
    ]

    all_x, all_y = [], []

    for idx, csv_path in enumerate(csv_files):
        x, y = read_columns(csv_path, x_col=0, y_col=1)
        if not x:
            print(f"Warning: no usable data in {csv_path}")
            continue
        all_x.extend(x)
        all_y.extend(y)

        style = line_styles[idx % len(line_styles)]
        basename = os.path.splitext(os.path.basename(csv_path))[0]
        plt.plot(x, y, style, linewidth=1.5, label=basename)

    if not all_x or not all_y:
        print("No valid data found in provided CSV files.")
        return

    xmin = min(v for v in all_x if v > 0)
    ymin = min(all_y)

    # Labels & grid
    plt.xlabel('Dictionary size', fontsize=12)
    plt.ylabel('Extrapolated compression ratio', fontsize=12)
    plt.grid(True, which='both', alpha=0.3)

    # "zero" axes
    plt.axhline(y=ymin, color='k', linestyle='-', alpha=0.3)
    plt.axvline(x=xmin, color='k', linestyle='-', alpha=0.3)

    # Log scale with dense ticks
    plt.xscale('log')
    plt.xlim(left=xmin)
    plt.ylim(bottom=ymin)

    # Use LogLocator to show ticks at 1e3, 2e3, 3e3 ...
    ax = plt.gca()
    ax.xaxis.set_major_locator(LogLocator(base=10.0, subs=np.arange(1, 10)*0.1/0.1, numticks=100))
    ax.xaxis.set_major_formatter(FuncFormatter(decimal_notation_formatter))

    plt.setp(ax.get_xticklabels(), rotation=270, ha="center")
    # plt.setp(ax.get_xticklabels(), rotation=-45, ha="left")

    plt.legend(fontsize=10)
    plt.tick_params(axis='both', which='major', labelsize=10)

    out_name = "_".join([os.path.splitext(os.path.basename(f))[0] for f in csv_files]) + ".png"
    plt.tight_layout()
    plt.savefig(out_name, dpi=300, bbox_inches='tight')
    plt.show()
    print(f"Saved plot as {out_name}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python plot_csvs.py file1.csv file2.csv ...")
        sys.exit(1)
    main(sys.argv[1:])
