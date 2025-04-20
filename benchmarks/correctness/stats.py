#!/usr/bin/env python
# /// script
# requires-python = ">=3.10"
# dependencies = [
#     "matplotlib",
#     "pyqt6",
# ]
# ///

"""This program shows `hyperfine` benchmark results as a grouped box plot.

Quoting from the matplotlib documentation:
    The box extends from the lower to upper quartile values of the data, with
    a line at the median. The whiskers extend from the box to show the range
    of the data. Flier points are those past the end of the whiskers.
"""

import argparse
import json
import os
import numpy as np
import matplotlib.pyplot as plt

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("files", nargs='+', help="JSON files with benchmark results")
parser.add_argument("--title", help="Plot Title")
parser.add_argument("--sort-by", choices=["median"], help="Sort method")
parser.add_argument(
    "--labels", help="Comma-separated list of entries for the plot legend"
)
parser.add_argument("-o", "--output", help="Save image to the given filename.")

args = parser.parse_args()

all_times = []
all_labels = []
all_file_names = []

def remove_outliers(data):
    """Remove outliers using the IQR method"""
    q1 = np.percentile(data, 25)
    q3 = np.percentile(data, 75)
    iqr = q3 - q1
    lower_bound = q1 - 1.5 * iqr
    upper_bound = q3 + 1.5 * iqr
    return [x for x in data if lower_bound <= x <= upper_bound]

for file in args.files:
    with open(file, encoding="utf-8") as f:
        results = json.load(f)["results"]
    
    # Extract labels and times
    if args.labels:
        labels = args.labels.split(",")
    else:
        labels = [b["command"] for b in results]
    
    times = [b["times"] for b in results]

    # Remove outliers from each dataset before plotting
    times = [remove_outliers(time_data) for time_data in times]

    if args.sort_by == "median":
        medians = [np.median(time_data) for time_data in times]
        indices = sorted(range(len(labels)), key=lambda k: medians[k])
        labels = [labels[i] for i in indices]
        times = [times[i] for i in indices]
    
    all_times.append(times)
    all_labels = labels  # Assume labels are the same for each file
    all_file_names.append(os.path.basename(file).split(".")[0])  # Group name is file name

# Set the number of boxes per group (same for all files)
num_boxes_per_group = len(all_times[0])

# Calculate positions of each group (side by side with little gap between groups)
positions = []
gap = 1  # Control the gap between groups (set to 1 for tight grouping)
for i in range(len(all_times)):
    positions.extend([i * (num_boxes_per_group + gap) + j + 1 for j in range(num_boxes_per_group)])

# Flatten the list of times to make box plot data
flat_times = [item for sublist in all_times for item in sublist]

# Assign colors to each label (same color for same label across groups)
cmap = plt.get_cmap("rainbow")
color_map = {label: cmap(i / len(all_labels)) for i, label in enumerate(all_labels)}

# Create the grouped box plot
plt.figure(figsize=(12, 6), constrained_layout=True)

boxplot = plt.boxplot(flat_times, positions=positions, vert=True, patch_artist=True)

# Assign colors for each box plot based on the labels
for patch, label in zip(boxplot["boxes"], flat_times):
    label_idx = flat_times.index(label)
    patch.set_facecolor(color_map[all_labels[label_idx]])

# Set the labels and title
if args.title:
    plt.title(args.title)

# Set x-tick labels as JSON file names, grouped side by side
xticks = [i * (num_boxes_per_group + gap) + num_boxes_per_group / 2 for i in range(len(all_file_names))]
plt.xticks(xticks, all_file_names, rotation=45)

# Add legend for the box plots
plt.legend(handles=boxplot["boxes"], labels=all_labels, loc="best", fontsize="medium")

plt.ylabel("Time [s]")
plt.ylim(0, None)

# Save or show the plot
if args.output:
    plt.savefig(args.output)
else:
    plt.show()
