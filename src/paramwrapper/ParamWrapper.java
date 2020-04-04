/**
 *
 */
package paramwrapper;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

import fdtmc.FDTMC;

/**
 * Façade to a PARAM executable.
 *
 * @author Thiago
 *
 */
public class ParamWrapper implements ParametricModelChecker {
    private static final Logger LOGGER = Logger.getLogger(ParamWrapper.class.getName());

	private String paramPath;
	private IModelCollector modelCollector;
	private boolean usePrism = false;

    public ParamWrapper(String paramPath) {
        this(paramPath, new NoopModelCollector());
    }

    public ParamWrapper(String paramPath, IModelCollector modelCollector) {
        this.paramPath = paramPath;
        this.usePrism = paramPath.contains("prism");
        this.modelCollector = modelCollector;
    }

	public String fdtmcToParam(FDTMC fdtmc) {
		ParamModel model = new ParamModel(fdtmc);
		modelCollector.collectModel(model.getParametersNumber(), model.getStatesNumber());
		return model.toString();
	}

	@Override
	public String getReliability(FDTMC fdtmc) {
	    ParamModel model = new ParamModel(fdtmc);
        modelCollector.collectModel(model.getParametersNumber(), model.getStatesNumber());
		String modelString = model.toString();

		if (usePrism) {
		    modelString = modelString.replace("param", "const");
		}
		String reliabilityProperty = "P=? [ F \"success\" ]";

		return evaluate(modelString, reliabilityProperty, model);
	}

	private String evaluate(String modelString, String property, ParamModel model) {
		try {
		    LOGGER.finer(modelString);
			File modelFile = File.createTempFile("model", "param");
			FileWriter modelWriter = new FileWriter(modelFile);
			modelWriter.write(modelString);
			modelWriter.flush();
			modelWriter.close();

			File propertyFile = File.createTempFile("property", "prop");
			FileWriter propertyWriter = new FileWriter(propertyFile);
			propertyWriter.write(property);
			propertyWriter.flush();
			propertyWriter.close();

			File resultsFile = File.createTempFile("result", null);

			String formula;
			long startTime = System.nanoTime();
			if (usePrism && !modelString.contains("const")) {
			    formula = invokeModelChecker(modelFile.getAbsolutePath(),
			                                 propertyFile.getAbsolutePath(),
			                                 resultsFile.getAbsolutePath());
			} else if(usePrism) {
			    formula = invokeParametricPRISM(model,
			                                    modelFile.getAbsolutePath(),
                                                propertyFile.getAbsolutePath(),
                                                resultsFile.getAbsolutePath());
			} else {
			    formula = invokeParametricModelChecker(modelFile.getAbsolutePath(),
			                                           propertyFile.getAbsolutePath(),
			                                           resultsFile.getAbsolutePath());
			}
			long elapsedTime = System.nanoTime() - startTime;
            modelCollector.collectModelCheckingTime(elapsedTime);
			return formula.trim().replaceAll("\\s+", "");
		} catch (IOException e) {
			LOGGER.log(Level.SEVERE, e.toString(), e);
		}
		return "";
	}

	private String invokeParametricModelChecker(String modelPath,
												String propertyPath,
												String resultsPath) throws IOException {
		String commandLine = paramPath+" "
							 +modelPath+" "
							 +propertyPath+" "
							 +"--result-file "+resultsPath;
		return invokeAndGetResult(commandLine, resultsPath+".out");
	}

    private String invokeParametricPRISM(ParamModel model,
                                         String modelPath,
                                         String propertyPath,
                                         String resultsPath) throws IOException {
        String commandLine = paramPath+" "
                             +modelPath+" "
                             +propertyPath+" "
                             +"-exportresults "+resultsPath+" "
                             +"-param "+String.join(",", model.getParameters());
        String rawResult = invokeAndGetResult(commandLine, resultsPath);
        int openBracket = rawResult.indexOf("{");
        int closeBracket = rawResult.indexOf("}");
        String expression = rawResult.substring(openBracket+1, closeBracket);
        return expression.trim().replace('|', '/');
    }

	private String invokeModelChecker(String modelPath,
									  String propertyPath,
									  String resultsPath) throws IOException {
		String commandLine = paramPath+" "
				 			 +modelPath+" "
				 			 +propertyPath+" "
				 			 +"-exportresults "+resultsPath;
		return invokeAndGetResult(commandLine, resultsPath);
	}

	private String invokeAndGetResult(String commandLine, String resultsPath) throws IOException {
	    LOGGER.fine(commandLine);
		Process program = Runtime.getRuntime().exec(commandLine);
		int exitCode = 0;
		try {
			exitCode = program.waitFor();
		} catch (InterruptedException e) {
			LOGGER.severe("Exit code: " + exitCode);
			LOGGER.log(Level.SEVERE, e.toString(), e);
		}
		List<String> lines = Files.readAllLines(Paths.get(resultsPath), Charset.forName("UTF-8"));
		lines.removeIf(String::isEmpty);
		// Formula
		return lines.get(lines.size()-1);
	}

}
