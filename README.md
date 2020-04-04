# ReAna
**Re**liability **Ana**lysis of Software Product Lines

ReAna is a tool that takes variability-aware UML behavioral models annotated
with components' reliabilities as input and outputs a family-wide reliability.
In order to accomplish this, it uses a feature-family-based approach to model-checking
of SPLs.


## Building

All required dependencies are in the `libs` folder:

- jcudd.jar: a Java binding to [CUDD](http://vlsi.colorado.edu/~fabio/CUDD/) 2.5.1.
    The jar was created with [JNAerator](https://code.google.com/p/jnaerator/), and the CUDD shared library is bundled inside the jar.
- jep-2.23-custom.jar: a customized version of [JEP](http://www.cse.msu.edu/SENS/Software/jep-2.23/doc/website/doc/doc_usage.htm) 2.23
    which allows overriding standard arithmetic operators (e.g., +, -). The modified source code
    is available at https://github.com/SPLMC/jep.
- jopt-simple-4.9.jar: [JOpt Simple](https://pholser.github.io/jopt-simple/), a library for command-line
    argument parsing.


## Running

The tool accepts a number of command-line arguments which provide for some degree of configuration:

- `--analysis-strategy` (defaults to *FEATURE_FAMILY*): the analysis strategy to be used. Can be one of:
    FEATURE_FAMILY | FEATURE_PRODUCT | FAMILY | FAMILY_PRODUCT | PRODUCT.
- `--feature-model` (defaults to _fm.txt_): a text file with the feature model for the SPL to be analyzed represented in
    Conjunctive Normal Form (CNF) using Java logical operators. This representation can be obtained
    from a feature diagram using FeatureIDE's _Export to CNF_ functionality.
- `--uml-models` (defaults to _modeling.xml_): an XML file containing the UML behavioral models (Activity and Sequence Diagrams)
    to be analyzed. Currently the only accepted format is the one used by the MagicDraw tool.
- `--param-path` (defaults to _/opt/param-2-3-64_): the directory of the parametric model checker (PARAM or Prism) installation.
- `--configurations-file` (defaults to _configurations.txt_): path to a file with a comma-separated list of
    features per line, each corresponding to a configuration for which the reliability is wanted.
- `--configuration`: alternatively, it is possible to specify a single configuration inline. Overrides `--configurations-file`.
- `--all-configurations`: causes the tool to dump all possible configurations and corresponding reliabilities.
    Overrides `--configuration` and `--configurations-file`.
- `--concurrency-strategy` (defaults to _PARALLEL_): Run parallelizable computations concurrently (PARALLEL) or sequentially (SEQUENTIAL).
- `--pruning-strategy` (defaults to _FM_): The strategy that should be used for pruning invalid configurations
    during partial evaluations. Can be one of: FM (whole feature model); NONE (no pruning).
- `--stats`: Prints profiling statistics such as wall-clock time and used memory.
- `--suppress-report`: Suppress reliabilities report for all evaluated configurations. Useful when analyzing an SPL
    with a large configuration space.


After the run, if the applied strategy was the feature-family-based one, an Algebraic Decision Diagram (ADD)
representing the possible reliabilities for the SPL is dumped to a DOT file named _family-reliability.dot_.
