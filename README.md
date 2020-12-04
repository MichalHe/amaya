This is an work-in-progress implementation of algorithms working with pressburger arithmetics using finite automatons.

## How to render graphs from SMT Library language into graphviz(dot)
First of all make sure that you have installed all packages from `requirements.txt` file. It is recommended to use virtual env 
to manage python app dependencies. Afterwards run following command (replace `<your_input_file>` with the path to the file containing inequality):
```sh
python3 ./make_digraph.py -i <your_input_file>
```

By default the script reads from stdin, but by passing `-i` flag, provided file is read instead. The output is to stdout.
For more information run: 
```sh
python3 ./make_digraph.py --help
```
