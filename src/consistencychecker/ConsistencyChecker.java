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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.dllearner.utilities.owl.OWLAPIRenderers;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.ocl.ParserException;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.HermiT.Reasoner.ReasonerFactory;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import com.clarkparsia.owlapi.explanation.BlackBoxExplanation;
import com.clarkparsia.owlapi.explanation.HSTExplanationGenerator;

import ecorexmiparser.TLink;
import ecorexmiparser.TObject;
import util.Constants;

/**
 * Represents an Ecore model consistency checker based on the mapping described
 * by Calvanesi et al. Daniela Berardia, Diego Calvanese, Giuseppe De Giacomoa,
 * Reasoning on UMLclass diagrams Artificial Intelligence, Volume 168, October
 * 2005
 * 
 * @author Cassio Santos, Christiano Braga
 * @version 1.0.0
 * @since 1.0.0
 * @see <a href="http://dx.doi.org/10.1016/j.artint.2005.05.003" target=
 *      _blank>http://dx.doi.org/10.1016/j.artint.2005.05.003</a>
 */
public class ConsistencyChecker {

	private static final String LOG_INITIALIZING_ONTOLOGY_CREATOR = "\nInitializing OntologyCreator.";
	private static final String LOG_STARTING_ONTOLOGY_CREATION = "\nStarting ontology creation.";
	private static final String LOG_ENDED_ONTOLOGY_CREATION = "\nEnded ontology creation.";
	private static final String LOG_ONTOLOGY_NULL = "\nThe ontology created is now null.";
	private static final String LOG_CREATING_REASONER = "\nCreating the reasoner with the ontology information.";
	private static final String LOG_REASONER_NULL = "\nThe reasoner created is now null.";
	private static final String LOG_CREATED_REASONER = "\nThe reasoner was created.";
	private static final String LOG_EXECUTION_TERMINATES = "\nThe execution was terminated with the error: \"%s\" ";
	private static final String CONSISTENCY_CHECKER_ONTOLOGY_ERROR = "Unable to create ontology.";
	private static final String CONSISTENCY_CHECKER_REASONER_ERROR = "Unable to create reasoner.";
	private static final String CONSISTENCY_CHECKER_REASONER_NOT_CREATED_ERROR = "To reason on a ontology you must first instantiate the reasoner.";
	private static final String CONSISTENCY_CHECKER_NOT_REASONED_ERROR = "To check a ontology consistency, you must first reason on it.";
	private static final String CONSISTENCY_CHECKER_NOT_CHECKED_ERROR = "Consistency was not checked.";
	private static final String NO_REASONING_TECHNIQUES_APPLIED_ERROR = "Reasoning techniques was not applied.";
	
	private OntologyCreator creator;
	private OWLOntology ontology;
	private Reasoner reasoner;
	private Set<OWLClass> inconsistent_classes;
	private boolean isChecked = false;

	public ConsistencyChecker(EPackage metaModel, Map<String, ArrayList<TObject>> simplified,
			Map<String, ArrayList<TObject>> obPool, Map<String, HashMap<TObject, ArrayList<TLink>>> linkPool,
			StringBuilder log)
					throws ConsistencyCheckerGenericException, OWLOntologyCreationException, ParserException {
		creator = new ExtendedOntologyCreator();
		creator.processAndCreateOntology(metaModel, log);

		ontology = ((ExtendedOntologyCreator) creator).extendOntology(simplified, obPool, linkPool);
		if (ontology == null) {
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_ONTOLOGY_ERROR);
		} else {
			reasoner = new Reasoner(ontology);
			if (reasoner == null) {
				throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_REASONER_ERROR);
			}
		}
	}

	public ConsistencyChecker(EPackage pkg, StringBuilder log)
			throws ConsistencyCheckerGenericException, OWLOntologyCreationException, ParserException {
		creator = new OntologyCreator();
		ontology = creator.processAndCreateOntology(pkg, log);
		if (ontology == null) {
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_ONTOLOGY_ERROR);
		} else {
			reasoner = new Reasoner(ontology);
			if (reasoner == null) {
				throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_REASONER_ERROR);
			}
		}
	}

	public ConsistencyChecker(String m, StringBuilder log)
			throws ConsistencyCheckerGenericException, OWLOntologyCreationException, ParserException {
		log.append(LOG_INITIALIZING_ONTOLOGY_CREATOR);
		creator = new OntologyCreator();
		log.append(LOG_STARTING_ONTOLOGY_CREATION);
		ontology = creator.processAndCreateOntology(m, log);
		log.append(LOG_ENDED_ONTOLOGY_CREATION);
		if (ontology == null) {
			log.append(LOG_ONTOLOGY_NULL);
			log.append(String.format(LOG_EXECUTION_TERMINATES, CONSISTENCY_CHECKER_ONTOLOGY_ERROR));
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_ONTOLOGY_ERROR);
		} else {
			log.append(LOG_CREATING_REASONER);
			reasoner = new Reasoner(ontology);
			if (reasoner == null) {
				log.append(LOG_REASONER_NULL);
				throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_REASONER_ERROR);
			}
			log.append(LOG_CREATED_REASONER);
		}
	}

	public ConsistencyChecker(String mM, String oM, StringBuilder log)
			throws ConsistencyCheckerGenericException, OWLOntologyCreationException, ParserException {
		creator = ExtendedOntologyCreator.getInstance();
		creator.processAndCreateOntology(mM, log);
		ontology = ((ExtendedOntologyCreator) creator).extendOntology(oM);

		if (ontology == null) {
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_ONTOLOGY_ERROR);
		} else {
			reasoner = new Reasoner(ontology);
			if (reasoner == null) {
				throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_REASONER_ERROR);
			}
		}
	}

	/**
	 * @return Returns the working ontology
	 */
	public OWLOntology getOntology() {
		return ontology;
	}

	public void reason() throws ConsistencyCheckerGenericException {
		if (reasoner == null) {
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_REASONER_NOT_CREATED_ERROR);
		} else {
			reasoner.isConsistent();
			isChecked = true;
		}
	}

	/**
	 * Checks if the ontology associated with a model is consistent. Hermit
	 * returns a set of inconsistent classes when
	 * getUnsatisfiableClasses().getEntitiesMinusBottom() ; is called. If this
	 * set is empty our model is consistent and inconsistent otherwise.
	 * 
	 * @throws ConsistencyCheckerGenericException
	 * @return Returns true if the model is consistent and false otherwise
	 * 
	 */
	protected boolean checkConsistency() throws ConsistencyCheckerGenericException {
		// if (reasoner == null) {
		// throw new
		// ConsistencyCheckerException(CONSISTENCY_CHECKER_REASONER_ERROR);
		// } else {
		// reasoner.isConsistent();
		// isChecked = true;
		if (isChecked) {
			inconsistent_classes = reasoner.getUnsatisfiableClasses().getEntitiesMinusBottom();
			return inconsistent_classes.isEmpty();
		} else {
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_NOT_REASONED_ERROR);
		}
	}

	/**
	 * Once the consistency of the model was checked, this method returns the
	 * explanation for the inconsistency.
	 * 
	 * @return Returns an automatic explanation from the Hermit Reasoner about
	 *         the inconsistencies found in the ontology.
	 * @throws ConsistencyCheckerGenericException
	 */
	protected HashMap<OWLClass, Set<Set<String>>> explain(boolean all) throws ConsistencyCheckerGenericException {
		HashMap<OWLClass, Set<Set<String>>> fullMapClassExplanation = new HashMap<OWLClass, Set<Set<String>>>();
		if (!isChecked) {
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_NOT_CHECKED_ERROR);
		} else {
			ReasonerFactory factory = new Reasoner.ReasonerFactory() {
				protected OWLReasoner createHermiTOWLReasoner(org.semanticweb.HermiT.Configuration configuration,
						OWLOntology ontology) {
					configuration.throwInconsistentOntologyException = false;
					return new Reasoner(configuration, ontology);
				}
			};
			HSTExplanationGenerator multExplanator = new HSTExplanationGenerator(
					new BlackBoxExplanation(ontology, factory, reasoner));
			// Now we can get explanations for the inconsistency
			Set<OWLAxiom> explanations = null;
			Set<Set<OWLAxiom>> allExplanations = null;
			for (OWLClass cls : reasoner.getUnsatisfiableClasses().getEntitiesMinusBottom()) {
				HashSet<Set<String>> fullans = new HashSet<Set<String>>();
				if (all) {
					allExplanations = multExplanator.getExplanations(cls);
					for (Set<OWLAxiom> explanationss : allExplanations) {
						HashSet<String> temp = new HashSet<String>();
						for (OWLAxiom causingAxiom : explanationss) {
							temp.add(OWLAPIRenderers.toManchesterOWLSyntax(causingAxiom));
						}
						fullans.add(temp);
					}
				} else {
					HashSet<String> ans = new HashSet<String>();
					explanations = multExplanator.getExplanation(cls);
					for (OWLAxiom causingAxiom : explanations) {
						ans.add(OWLAPIRenderers.toManchesterOWLSyntax(causingAxiom));
					}
					fullans.add(ans);
				}
				fullMapClassExplanation.put(cls, fullans);
			}
		}
		return fullMapClassExplanation;
	}

	/**
	 * Once the consistency of the model was checked, this method returns the
	 * equivalent classes reasoned by Pellet
	 * 
	 * @return Returns Sets of equivalent classes names.
	 * @throws ConsistencyCheckerGenericException
	 */
	protected ArrayList<ArrayList<String>> getEquivalentClasses() throws ConsistencyCheckerGenericException {
		if (!isChecked) {
			throw new ConsistencyCheckerGenericException(NO_REASONING_TECHNIQUES_APPLIED_ERROR);
		}
		HashMap<String, Boolean> classes = new HashMap<>();
		ArrayList<ArrayList<String>> classesDeEquivalencia = new ArrayList<ArrayList<String>>();
		for (OWLClass cls : ontology.getClassesInSignature(true)) {
			if (classes.get(cls.getIRI().toString()) == null) {
				classes.put(cls.getIRI().toString(), Boolean.TRUE);
				ArrayList<String> equivalence = new ArrayList<String>();

				for (OWLClass c : reasoner.getEquivalentClasses((OWLClassExpression) cls)) {
					String[] splittedclsName = c.getIRI().toString().split(Constants.HASH);
					equivalence.add(splittedclsName[splittedclsName.length - 1]);
					classes.put(c.getIRI().toString(), Boolean.TRUE);
				}
				classesDeEquivalencia.add(equivalence);
			}
		}
		return classesDeEquivalencia;
	}

	/**
	 * Once the consistency of the model was checked, this method returns the
	 * inconsistent classes reasoned by Pellet
	 * 
	 * @return Returns the inconsistent classes names.
	 * @throws ConsistencyCheckerGenericException
	 */
	protected ArrayList<String> getInconsistentClassesNames() throws ConsistencyCheckerGenericException {
		ArrayList<String> cls = new ArrayList<String>();

		if (!isChecked) {
			throw new ConsistencyCheckerGenericException(CONSISTENCY_CHECKER_NOT_CHECKED_ERROR);
		} else {
			for (OWLClass iter : inconsistent_classes) {
				cls.add(iter.toString());
			}
			return cls;
		}
	}

	/**
	 * 
	 * @param owlFilepath
	 *            The full path to where the .owl File must be generated
	 * @throws OWLOntologyStorageException
	 * @throws ConsistencyCheckerGenericException
	 */
	public void save(String owlFilepath) throws OWLOntologyStorageException, ConsistencyCheckerGenericException {
		creator.save(owlFilepath, ontology);
	}
}
