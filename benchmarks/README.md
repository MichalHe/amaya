# SMT benchmarking platform

## Installing Dependencies
```
pip3 install -r requirements.txt
```

## How to run

```
cat benchmarks.input | ./pycobench -c config.yaml -j JOBS -t TIMEOUT -o OUTPUT_FILE
```
When the benchmarks finish, you can process the results by
```
cat OUTPUT_FILE | ./pyco_proc --csv > OUTPUT_CSV
```
