/**
 *   This file is part of ECore Consistency Checker (ECC).
 *
 *   ECC is a free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   ECC is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with ECC.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */

package consistencychecker;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.HashMap;
import java.util.Set;

import org.eclipse.ocl.ParserException;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

import util.Constants;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.1.0
 * @since 1.0.0
 */
public class Main {

	// Valid command line parameters
	private static final String MINUS_OWL = "-owl";
	private static final String MINUS_EXTEND = "-extend";
	private static final String MINUS_EXPLAIN = "-explain";
	private static final String MINUS_EXPLAINALL = "-explainall";
	private static final String MINUS_EQUIV = "-equiv";
	private static final String MINUS_LOG = "-log";
	private static final String MINUS_HELP = "-help";

	// Set of extensions handled in ECC
	private static final String ECORE_EXTENSION = ".ecore";
	private static final String OWL_EXTENSION = ".owl";
	private static final String XMI_EXTENSION = ".xmi";

	// Help messages
	private static final String HELP_USAGE = "usage: java -jar consistencyChecker [-owl] [-equiv] [-explain] [-extend] [input_objectModel.xmi] input_ClassDiagram.ecore \nusage: java -jar consistencyChecker [-help]";
	private static final String HELP_OWL = "-owl:\n\t Creates a OWL file of the ontology with name: input_file.owl.";
	private static final String HELP_EXPLAIN = "-explain:\n\t Display an automatic explanation from the reasoner about the inconsistencies found in the ontology.";
	private static final String HELP_EXPLAINALL = "-explainall:\n\t Display all the automatic explanations from the reasoner about the inconsistencies found in the ontology.";
	private static final String HELP_EQUIV = "-equiv:\n\t Display the equivalence classes reasoned by the reasoner.";
	private static final String HELP_EXTENDED = "-extend:\n\t Informes that the following parameter is a object model from the input class diagram.";
	private static final String HELP_HELP = "-help:\n\t Display this message.";
	private static final String HELP_ACKS_MAIN_MESSAGE = "\nThis sofware uses the following libraries:";
	private static final String HELP_ACKS_HERMIT = "HermiT Reasoner";
	private static final String HELP_ACKS_DLLEARNER = "DL-Learner";
	private static final String HELP_ACKS_AVAILABLE = "Available at:";
	private static final String HELP_ACKS_AVAILABLE_HERMIT = "http://www.hermit-reasoner.com/";
	private static final String HELP_ACKS_AVAILABLE_DLLEARNER = "http://www.dl-learner.org/Projects/DLLearner";

	// (In)Consistency messages
	private static final String MODEL_CONSISTENT = "The model %s is consistent";
	private static final String MODEL_INCONSISTENT = "The model %s is inconsistent";
	private static final String INCONSISTENTCLASSES = "The folowing classes are inconsistent";
	private static final String INCONSISTENCYEXPLANATION = "The following axioms make %s class inconsistent:";

	// Error Message
	private static final String FINAL_PARAM_ERR = "The final parameter must be a .ecore model or the -help parameter. \nFor more detailed instructions please use the -help parameter.";
	private static final String UNKNOW_PARAM_ERR = "The parameter %s is unknow. Plese use the -help parameter to get a list of valids parameters.";
	private static final String UNKNOW_XMI_ERR = "The parameter after the \"-extend\" parameter must be an .xmi model";
	private static final String PARAM_ERR = "Incorrect number of parameters, please provide the model name. \nFor more detailed instructions please add the -help parameter.";
	private static final String ONTOLOGY_CREATOR_ILL_FORMED_MODEL_ERROR = "The model is not well-formed.";

	// Explain Parameter messages
	private static final String CONSISTENCY_EXPLANATION = "The model is consistent, no explanation was generated.";
	private static final String ONE_POSSIBLE_EXPLATION = "One possible explanation for %s inconsistency:";

	// Utils
	private static final String NOTHING = "Nothing";
	private static final String NOT = "not";
	private static final String SEPARATOR = System.getProperty("path.separator");
	private static final String JUMP_LINE = "\n";

	// Save Parameter messages
	private static final String MODEL_SAVED = "Model saved as: %s";

	// Equiv Parameter messages
	private static final String EQUIVALENCE_CLASSES = "\nEquivalence Classes:";
	private static final String EMPTY_ONTOLOGY = "The resulting ontology is empty, no equivalence message was generated";

	// LOG messages
	private static final String LOG_INITIALIZING = "Initializing consistencychecker at: ";
	private static final String LOG_CHECK_PARAMETERS = "\nChecking command line parameters.";
	private static final String LOG_PARAM_UNDER_ONE = "\nThere are no parameters, at least the .ecore model must be informed.";
	private static final String LOG_EXECUTION_TERMINATES = "\nThe execution was terminated with the error: \"%s\" ";
	private static final String LOG_NOT_ECORE = "\nThe final parameter was not an .ecore model.";
	private static final String LOG_OWL_FOUND = "\nThe parameter -owl was detected.";
	private static final String LOG_EXTEND_FOUND = "\nThe parameter -extend was detected.";
	private static final String LOG_EXPLAIN_FOUND = "\nThe parameter -explain was detected.";
	private static final String LOG_EXPLAINALL_FOUND = "\nThe parameter -explainall was detected.";
	private static final String LOG_EQUIV_FOUND = "\nThe parameter -equiv was detected.";
	private static final String LOG_LOG_FOUND = "\nThe parameter -log was detected.";
	private static final String LOG_UNKNOW_PARAM = "\nA unknow parameter was found.";
	private static final String LOG_RELATIVE_PATH = "\nThe relative path to the .ecore model is: ";
	private static final String LOG_MODEL_NAME = "\nThe .ecore file name is: ";
	private static final String LOG_INITIALIZE_SIMPLE_CCHECKER = "\nInitializing simple consistency checker";
	private static final String LOG_INITIALIZE_EXTENDED_CCHECKER = "\nInitializing extended consistency checker";
	private static final String LOG_READY_TO_REASON = "\nStarting reasoning on the created ontology.";
	private static final String LOG_DONE_REASONING = "\nReasoning completed.";
	private static final String LOG_SAVING_OWL = "\nReady to generate .owl representation of the ontology on the relative path: ";
	private static final String LOG_SAVED_OWL = "\nGeneration completed.";
	private static final String LOG_CHECKING_CONSISTENCY = "\nChecking the model consistency.";
	private static final String LOG_CREATING_EXPLANATION_MESSAGE = "\nAs requested creating explanation message.";
	private static final String LOG_CREATED_EXPLANATION_MESSAGE = "\nExplantion message created.";
	private static final String LOG_STARTING_PRINTING_EXPLANATION = "\nStarting to print explanation message.";
	private static final String LOG_ENDED_PRINTING_EXPLANATION = "\nEnded explanation message printing.";
	private static final String LOG_EXPLANTION_ON_CLASS = "\nPrinting explanation on concept: ";
	private static final String LOG_ONE_EXPLANATION = "\nOne explanation on the inconsistency of the concept ";
	private static final String LOG_CREATING_EQUIVALENCE_MESSAGE = "\nAs requested creating equivalence classes message.";
	private static final String LOG_CREATED_EQUIVALENCE_MESSAGE = "\nEquivalence classes message created.";
	private static final String LOG_STARTING_PRINTING_EQUIVALENCE = "\nStarting to print equivalence classes message.";
	private static final String LOG_ENDED_PRINTING_EQUIVALENCE = "\nEnded equivalence classes message printing.";

	private static ConsistencyChecker checker = null;
	private static String file_name;

	/**
	 * Standard use of ECC, as a stand-alone command line application will
	 * follow be handled by this function
	 * 
	 * @param args
	 *            Command line arguments feed though standard input
	 * @throws OWLOntologyStorageException
	 * @throws ConsistencyCheckerGenericException
	 *             In case of untreated but predictable exceptions
	 * @throws OWLOntologyCreationException
	 * @throws ParserException
	 * @throws IOException
	 *             In case of diagram model or object model can't be correctly
	 *             opened
	 */
	public static void main(String[] args) throws OWLOntologyStorageException, ConsistencyCheckerGenericException,
			OWLOntologyCreationException, ParserException, IOException {
		// Initializes Log variable
		StringBuilder log = new StringBuilder();
		// Initialize input file variable as an empty string
		String input_file = Constants.EMPTY_STRING;
		// Initialize final parameter variable as an empty string
		String final_parameter = Constants.EMPTY_STRING;

		log.append((LOG_INITIALIZING + Calendar.getInstance().getTime()));
		log.append(LOG_CHECK_PARAMETERS);
		// Checks if the parameters are well-formed
		if (args.length < 1) {
			log.append(LOG_PARAM_UNDER_ONE);
			log.append(String.format(LOG_EXECUTION_TERMINATES, PARAM_ERR));
			// The number of parameters must be >= 1
			System.err.println(PARAM_ERR);
			System.exit(0);
		} else {
			final_parameter = args[args.length - 1];
			if (final_parameter.equals(MINUS_HELP)) {
				// The final parameter was help, so print all help messages
				// on the standard out
				System.out.println(HELP_USAGE);
				System.out.println(HELP_EXTENDED);
				System.out.println(HELP_OWL);
				System.out.println(HELP_EXPLAIN);
				System.out.println(HELP_EXPLAINALL);
				System.out.println(HELP_EQUIV);
				System.out.println(HELP_HELP);
				System.out.println(HELP_ACKS_MAIN_MESSAGE);
				System.out.println(HELP_ACKS_HERMIT);
				System.out.println(HELP_ACKS_DLLEARNER);
				System.out.println(HELP_ACKS_AVAILABLE);
				System.out.println(HELP_ACKS_AVAILABLE_HERMIT);
				System.out.println(HELP_ACKS_AVAILABLE_DLLEARNER);
				System.exit(0);
			} else {
				if (!final_parameter.endsWith(ECORE_EXTENSION)) {
					log.append(LOG_NOT_ECORE);
					log.append(String.format(LOG_EXECUTION_TERMINATES, FINAL_PARAM_ERR));
					// The final parameter was not help nor an .ecore file, so
					// prints error and exits
					System.out.println(FINAL_PARAM_ERR);
					System.exit(0);
				} else {
					// Assigns the last parameter to the input file variable
					input_file = final_parameter;
				}
			}
		}

		// Checks the presence of the parameters
		boolean contains_owl = false;
		boolean contains_explain = false;
		boolean contains_explainall = false;
		boolean contains_equiv = false;
		boolean contains_log = false;
		// This variable will store the position of the object model.
		// If it remains -1 the parameter "extend" is not present.
		int contains_extends = -1;
		// Run through the command line attributes, setting Its respective
		// "contains" variables to true if they're present
		for (int i = 0; i < args.length - 1; i++) {
			switch (args[i].toLowerCase()) {
			case MINUS_OWL:
				log.append(LOG_OWL_FOUND);
				contains_owl = true;
				break;
			case MINUS_EXPLAIN:
				log.append(LOG_EXPLAIN_FOUND);
				contains_explain = true;
			case MINUS_EQUIV:
				log.append(LOG_EQUIV_FOUND);
				contains_equiv = true;
			case MINUS_EXTEND:
				log.append(LOG_EXTEND_FOUND);
				// Stores the object model position in the
				// "contain_extends" variable
				// And increases the loop counter
				contains_extends = ++i;
				if (!args[i].toLowerCase().endsWith(XMI_EXTENSION)) {
					// If the parameter after the "-extend" is not
					// an XMI File
					// Than an error is printed and the program is
					// terminated
					System.err.println(String.format(UNKNOW_XMI_ERR, args[i]));
					System.exit(-1);
				}
				break;
			case MINUS_EXPLAINALL:
				log.append(LOG_EXPLAINALL_FOUND);
				contains_explainall = true;
			case MINUS_LOG:
				log.append(LOG_LOG_FOUND);
				contains_log = true;
			default:
				// If there's no match no any parameter
				// An error is exhibited and the program is
				// terminated
				log.append(LOG_UNKNOW_PARAM);
				log.append(String.format(LOG_EXECUTION_TERMINATES, UNKNOW_PARAM_ERR));
				System.err.println(String.format(UNKNOW_PARAM_ERR, args[i]));
				System.exit(-1);
			}
		}

		// get the ECore model file name
		log.append(LOG_RELATIVE_PATH + input_file);
		file_name = input_file.split(SEPARATOR)[input_file.split(SEPARATOR).length - 1];
		log.append(LOG_MODEL_NAME + file_name);

		// Initiates the ConsistencyChecker, creates the ontology
		if (contains_extends == -1) {
			// If "contains_extends" equals -1, than no extension file is passed
			// as an argument
			log.append(LOG_INITIALIZE_SIMPLE_CCHECKER);
			checker = new ConsistencyChecker(input_file, log);
		} else {
			// If "contains_extends" is not equal to -1, than the object model
			// file is passed as an argument
			log.append(LOG_INITIALIZE_EXTENDED_CCHECKER);
			checker = new ConsistencyChecker(file_name, args[contains_extends], log);
		}
		// Saves the created ontology as an .owl file if request in command line
		// arguments
		if (contains_owl) {
			log.append(LOG_SAVING_OWL + input_file.replaceAll(ECORE_EXTENSION, OWL_EXTENSION));
			// The standard file name for the ".owl" representation is the same
			// file name
			// as the ECore file, only changing the extension.
			checker.save(input_file.replaceAll(ECORE_EXTENSION, OWL_EXTENSION));
			System.out.println(String.format(MODEL_SAVED, file_name.replaceAll(ECORE_EXTENSION, OWL_EXTENSION)));
			log.append(LOG_SAVED_OWL);
		}

		// Reason on the ontology.
		log.append(LOG_READY_TO_REASON);
		checker.reason();
		log.append(LOG_DONE_REASONING);

		// Displays the consistency check result
		String result_log = printConsistencyMessage();
		log.append(result_log);

		// Displays the explanation message if requested in command line
		// parameters
		if (contains_explain || contains_explainall) {
			String explain_result = printExplainMessage(contains_explainall);
			log.append(explain_result);
		}

		// Displays the equivalence classes if request in command line
		// parameters
		if (contains_equiv) {
			String equiv_result = printEquivalentClasses();
			log.append(equiv_result);
		}

		// If requested in command line, the Log file is generated.
		// This parameter is not exhibited in help / usage messages as is
		// intended
		// to be used for debbuging purposes only.
		if (contains_log) {
			BufferedWriter logFile = new BufferedWriter(new FileWriter(
					input_file.replaceAll(ECORE_EXTENSION, Calendar.getInstance().getTimeInMillis() + ".log")));
			logFile.write(log.toString());
			logFile.close();
		}
	}


	/**
	 * Displays the equivalence classes calculated in the current usage
	 * 
	 * @return Returns the logs messages genereted in the process.
	 */
	private static String printEquivalentClasses() {
		StringBuilder log = new StringBuilder();
		log.append(LOG_CREATING_EQUIVALENCE_MESSAGE);
		try {
			// Declares and sets the equivalentClasses variable
			ArrayList<ArrayList<String>> equivalencyClasses = checker.getEquivalentClasses();
			log.append(LOG_CREATED_EQUIVALENCE_MESSAGE);

			log.append(LOG_STARTING_PRINTING_EQUIVALENCE);
			// prints on the standard output if there are equivalent classes or
			// not
			if (equivalencyClasses.size() > 0) {
				log.append("\n" + EQUIVALENCE_CLASSES);
				System.out.println(EQUIVALENCE_CLASSES);
			} else {
				log.append("\n" + EMPTY_ONTOLOGY);
				System.out.println(EMPTY_ONTOLOGY);
			}

			// Print the equivalent classes as comma separeted lists
			// Each list is delimited by a pair of brackets and is exhibited in
			// one line
			for (ArrayList<String> arrayList : equivalencyClasses) {
				log.append("\n" + "[");
				System.out.print("[");
				for (int i = 0; i < arrayList.size(); i++) {
					if (i > 0) {
						log.append(",");
						System.out.print(",");
					}
					// To increase readability and preserve the language
					// used in publications on the subject, the class "Not"
					// is always exhibited as "Nothing"
					if (arrayList.get(i).equals(NOT)) {
						log.append(NOTHING);
						System.out.print(NOTHING);
					} else {
						log.append(arrayList.get(i));
						System.out.print(arrayList.get(i));
					}
				}
				log.append("]" + JUMP_LINE);
				System.out.print("]" + JUMP_LINE);
			}
			log.append(LOG_ENDED_PRINTING_EQUIVALENCE);
		} catch (ConsistencyCheckerGenericException e) {
			// Prints the stack trace in case of error
			e.printStackTrace();
		}
		return log.toString();
	}

	/**
	 * Checks the consistency of the ontology, and print inconsistent classes if
	 * any. This function requires that the checker attribute have been
	 * instantiated.
	 * 
	 * @throws ConsistencyCheckerGenericException
	 * @return Returns the logs messages genereted in the process.
	 */
	private static String printConsistencyMessage() throws ConsistencyCheckerGenericException {
		StringBuilder log = new StringBuilder();
		log.append(LOG_CHECKING_CONSISTENCY);
		// Verifies the model and/or object model consistency and
		// displays the appropriated message
		if (checker.checkConsistency()) {
			log.append("\n" + String.format(MODEL_CONSISTENT, file_name));
			System.out.println(String.format(MODEL_CONSISTENT, file_name));
		} else {
			// If the model is inconsistent the inconsistent classes
			// are also printed to help debug the model.
			log.append("\n" + String.format(MODEL_INCONSISTENT, file_name));
			System.out.println(String.format(MODEL_INCONSISTENT, file_name));
			log.append("\n" + INCONSISTENTCLASSES);
			System.out.println(INCONSISTENTCLASSES);
			for (String s : checker.getInconsistentClassesNames()) {
				log.append("\n" + s);
				System.out.println(s);
			}
		}
		return log.toString();
	}

	/**
	 * Displays an automatic explanation from the Reasoner about the
	 * inconsistencies found in the ontology.
	 * 
	 * @param all
	 *            Set to true to display all inconsistency explations for each
	 *            class. Set to false to display only one explanation per class.
	 * @throws ConsistencyCheckerGenericException
	 */
	private static String printExplainMessage(boolean all) throws ConsistencyCheckerGenericException {
		StringBuilder log = new StringBuilder();
		log.append(LOG_CREATING_EXPLANATION_MESSAGE);
		// Initializes the mapClassExplanation variable with the
		// inconsistency explanations generated by the reasoner. (agregated by
		// class)
		// The "all" parameter filters the explanations if set to false
		// exhibiting only the first explanation per class.
		HashMap<OWLClass, Set<Set<String>>> mapClassExplanation = checker.explain(all);
		if (mapClassExplanation.size() == 0) {
			System.out.println(CONSISTENCY_EXPLANATION);
		}
		log.append(LOG_CREATED_EXPLANATION_MESSAGE);

		log.append(LOG_STARTING_PRINTING_EXPLANATION);
		// The explanations are exhibited by class aggregation.
		// This first loop selects the inconsistent class
		for (OWLClass cls : mapClassExplanation.keySet()) {
			log.append(LOG_EXPLANTION_ON_CLASS + cls.getIRI());
			// Prints a message informing to each class the inconsistencies
			// exhibited refers to.
			System.out.println(String.format(INCONSISTENCYEXPLANATION, cls.getIRI()));
			// This secons loop selects the insconsistent explanation for the
			// select class.
			for (Set<String> axs : mapClassExplanation.get(cls)) {
				log.append(LOG_ONE_EXPLANATION + cls.getIRI());
				System.out.println(String.format(ONE_POSSIBLE_EXPLATION, cls.getIRI()));
				// Each explanation is composed by a set of axioms.
				// This third loop prints each axiom in the selected
				// explanation.
				for (String ax : axs) {
					log.append("\n" + ax);
					System.out.println(ax);
				}
			}
		}
		log.append(LOG_ENDED_PRINTING_EXPLANATION);
		return log.toString();
	}

	/**
	 * Prints list of formation errors and if/how they were recovered.
	 * 
	 * @param message
	 *            List of formation errors in the ecore model file.
	 */
	protected static void printMessageModelIllFormed(ArrayList<String> message) {
		// Initializes the variable responsible for holding the ill formedness
		// error string
		String errorMessage = ONTOLOGY_CREATOR_ILL_FORMED_MODEL_ERROR + JUMP_LINE;
		// loops through the message errors, concatenating one at each line
		for (String error : message) {
			errorMessage += error + JUMP_LINE;
		}
		// Prints on the standard output the resulting error message
		System.out.println(errorMessage);
	}
}
