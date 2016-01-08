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

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.emf.common.CommonPlugin;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EEnumLiteral;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EParameter;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.impl.EPackageImpl;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;
import org.eclipse.ocl.OCL;
import org.eclipse.ocl.ParserException;
import org.eclipse.ocl.ecore.CallOperationAction;
import org.eclipse.ocl.ecore.Constraint;
import org.eclipse.ocl.ecore.EcoreEnvironmentFactory;
import org.eclipse.ocl.ecore.SendSignalAction;
import org.eclipse.ocl.expressions.OCLExpression;
import org.eclipse.ocl.helper.OCLHelper;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLCardinalityRestriction;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDatatype;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;

import util.Constants;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 2.0.2
 * @since 0.1
 * 
 */
public class OntologyCreator {
	private static final String LOG_GATHERED_AXIOMS = "\nall axioms gathered in one ontology.";
	private static final String LOG_GATHERING_AXIOMS = "\nGathering all axioms in one ontology.";
	private static final String LOG_CREATING_AXIOMS_EREFERENCE = "\nStarting axiom generation for the EReference with ends \"%s\" and \"%s\".";
	private static final String LOG_CREATED_AXIOMS_EREFERENCE = "\nEnded axiom generation for the EReference with ends \"%s\" and \"%s\".";
	private static final String LOG_CREATING_AXIOMS_INHERITANCE = "\nStarting axiom generation for the inheritance in the class %s.";
	private static final String LOG_CREATED_AXIOMS_INHERITANCE = "\nEnded axiom generation for the inheritance in the class %s.";
	private static final String LOG_CREATING_AXIOMS_INVARIANT = "\nStarting axiom generation for the axiom number %d in the class %s.";
	private static final String LOG_CREATED_AXIOMS_INVARIANT = "\nEnded axiom generation for the axiom number %d in the class %s.";
	private static final String LOG_CHECKING_ECLASS_INVARIANTS = "\nThe class \"%s\" was identified with %d invariants. Starting processing.";
	private static final String LOG_CHECKING_ECLASS = "\nChecking EClass %s.";
	private static final String LOG_CHECKED_ECLASS = "\nChecked EClass %s.";
	private static final String LOG_CHECKING_ECLASS_ATTRIBUTES = "\nChecking attributes of the EClass %s.";
	private static final String LOG_CHECKING_ECLASS_METHODS = "\nChecking methods of the EClass %s.";
	private static final String LOG_CHECKED_ECLASS_ATTRIBUTES = "\nAll the attributes of the EClass %s were checked.";
	private static final String LOG_CHECKED_ECLASS_METHODS = "\nAll the methods of the EClass %s were checked.";
	private static final String LOG_CHECKING_ECLASS_ATTRIBUTES_DATA_TYPE = "\nThe attribute %s of the EClass %s, was identified as an OWLDataType attribute. Starting axiom generation.";
	private static final String LOG_CHECKING_ECLASS_ATTRIBUTES_NOT_DATA_TYPE = "\nThe attribute %s of the EClass %s, was identified as an non OWLDataType attribute. Starting axiom generation";
	private static final String LOG_ATTRIBUTE_AXIOM_GENERATION_FINISHED = "\nThe axiom generation for the attribute %s of the class %s was finished";
	private static final String LOG_GENERATING_ECLASS_METHODS_AXIOMS = "\nStarting axiom generation for the method %s in the class %s";
	private static final String LOG_GENERATED_ECLASS_METHODS_AXIOMS = "\nEnded axiom generation for the method %s in the class %s";
	private static final String LOG_CHECKING_ANNOTATIONS = "\nChecking class \"%s\" annotations.";
	private static final String LOG_CHECKED_ANNOTATIONS = "\nChecked all class \"%s\" annotations.";
	private static final String LOG_ADDED_CLASS_IN_POOL = "\nThe class \"%s\" was added in the classes pool.";
	private static final String LOG_GETTING_EPACKAGE = "\nExtracting EPackage name.";
	private static final String LOG_RUNNING_ELEMENTS = "\nStarting to pass by elements in EPackage.";
	private static final String LOG_ELEMENT_X = "\nClassifing element %s.";
	private static final String LOG_ELEMENT_X_AS_CLASS = "\nThe element %s was classified as a Class.";
	private static final String LOG_PARSING_EPACKAGE = "\nParsing elements from loaded EPackage.";
	private static final String LOG_PARSED_EPACKAGE = "\nDone Parsing elements from loaded EPackage.";
	private static final String LOG_LOADED_EPACKAGE = "\nLoading EPackage from the .ecore file.";
	private static final String LOG_CHECKING_WELL_FORMEDNESS = "\nChecking if the model is well-formed.";
	private static final String LOG_CHECKED_WELL_FORMEDNESS = "\nDone checking model well-formedness.";
	private static final String LOG_PRINTING_ERRORS = "\nThe model is not well-formed. Printing recovered errors.";
	private static final String LOG_PRINTED_ERRORS = "\nDone printing model recovered errors.";
	private static final String LOG_CREATING_ONTOLOGY = "\nCreating ontology based on the model parsed.";
	private static final String LOG_CREATED_ONTOLOGY = "\nDone creating the ontology.";
	private static final String LOG_PARSING_MODEL = "\nStarting to parse input model.";
	private static final String LOG_PARSED_MODEL = "\nDone parsing input model.";
	private static final String ERR_SAVE_NULL_ONTOLOGY = "The ontology can't be null at the save moment.";
	protected static final String NULL = "null";
	protected static final String ECORE_EXTENSION = "ecore";
	protected static final String SPACE = " ";
	protected static final String UNDERSCORE = "ecore";
	protected static final String ONTOLOGY_CREATOR_ASSOCIATION_ROLES_NOT_OPOSITE_ERROR = "Two given association roles are not oposite.";
	protected static final String ILL_FORMED_TYPELESS_ATTR_EXCEPTION = "The model has at least one attribute with no type, no recovery was possible.";
	protected static final String ILL_FORMED_TYPELESS_METHOD_PARAMETER_EXCEPTION = "The model has at least one method parameter with no type, no recovery was possible.";
	protected static final String ILL_FORMED_NAMELESS_CLASS_RECOVERED_ERROR = "There was a nameless Class, the name %s was assigned to this execution";
	protected static final String ILL_FORMED_NAMELESS_ATTR_RECOVERED_ERROR = "There was a nameless Attribute, the name %s was assigned to this execution";
	protected static final String ILL_FORMED_NAMELESS_METHOD_RECOVERED_ERROR = "There was a nameless Method, the name %s was assigned to this execution";
	protected static final String ILL_FORMED_NAMELESS_ASSOCIATION_RECOVERED_ERROR = "There was a nameless association, the name %s was assigned to this execution";
	protected static final String ILL_FORMED_ASSOCIATIONEND_MULTIPLICITY_ERROR = "There is a multiplicity error in the association end %s, no recovery was possible.";
	protected static final String ILL_FORMED_ASSOCIATIONEND_NO_OPOSITE = "There is a association %s with no oposite. No recovery was possible.";
	protected static final String POUND_SIGN = "#";
	protected static final String RETURN = "ret";
	protected static final String ontologyIRI = "lse.ic.uff.br/ontology";
	protected static final String CLASS_POSFIX = "class";
	protected static final String INDIVIDUAL_POSFIX = "individual";
	protected static final String ENUMERATION_POSFIX = "enumeration";
	protected static final String ROLE_POSFIX = "role";
	protected static final String ATTRIBUTE_POSFIX = "attribute";
	protected static final String METHOD_POSFIX = "method";
	protected static final String ASSOCIATION_POSFIX = "association";
	protected static final String PIVOT_URL = "http://www.eclipse.org/emf/2002/Ecore/OCL/Pivot";
	protected static final String XMICONTAINER = "XMIContainer";
	protected String PACKAGE_PREFIX = Constants.EMPTY_STRING;
	protected ArrayList<EReference> associations;
	protected HashMap<EClass, ArrayList<EClass>> inheritances;
	protected ArrayList<EClass> classes;
	protected ArrayList<EEnum> enumerations;
	protected OWLDataFactory owlDataFactory_;
	protected Set<OWLAxiom> axiomList_;
	protected OWLClass thing;
	protected IRI ontologyIRI_;
	protected static OntologyCreator instance;
	private OWLOntologyManager ontologyManager_;
	protected String CLASS_NAME_BUILDER = "";

	public OntologyCreator() throws OWLOntologyCreationException {
		ontologyManager_ = OWLManager.createOWLOntologyManager();
		owlDataFactory_ = ontologyManager_.getOWLDataFactory();
		axiomList_ = new HashSet<OWLAxiom>();
		ontologyIRI_ = IRI.create(ontologyIRI);
		thing = owlDataFactory_.getOWLThing();

	}

	/**
	 * Populates the each collection that represent an Ecore construction with
	 * the objects from the input_model
	 * 
	 * @param input_model
	 *            String with the path to the Ecore model to be checked
	 * @throws ParserException
	 */
	private void parse(String input_model, StringBuilder log) throws ParserException {
		log.append(LOG_LOADED_EPACKAGE);
		EPackageImpl pkg = load(input_model);
		log.append(LOG_PARSING_EPACKAGE);
		parse(pkg, log);
		log.append(LOG_PARSED_EPACKAGE);
	}

	/**
	 * Populates the each collection that represent an Ecore construction with
	 * the objects from the pkg
	 * 
	 * @param pkg
	 *            Root EPackage of the Ecore model to be checked
	 * @throws ParserException
	 */
	private void parse(EPackage pkg, StringBuilder log) throws ParserException {
		log.append(LOG_GETTING_EPACKAGE);
		PACKAGE_PREFIX = pkg.getName();
		CLASS_NAME_BUILDER = ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + "(" + "%s" + "[" + CLASS_POSFIX + "]" + ")";
		EList<EClassifier> elements = pkg.getEClassifiers();
		classes = new ArrayList<EClass>();
		associations = new ArrayList<EReference>();
		enumerations = new ArrayList<EEnum>();
		HashMap<EClass, ArrayList<EClass>> reverse_inheritances = new HashMap<EClass, ArrayList<EClass>>();

		log.append(LOG_RUNNING_ELEMENTS);
		for (EClassifier classifier : elements) {
			log.append(String.format(LOG_ELEMENT_X, classifier.getName()));
			if (classifier instanceof EClass && !((EClass) classifier).getName().equals(XMICONTAINER)) {
				log.append(String.format(LOG_ELEMENT_X_AS_CLASS, classifier.getName()));
				log.append(String.format(LOG_ADDED_CLASS_IN_POOL, classifier.getName()));
				classes.add((EClass) classifier);

				ArrayList<EClass> superClasses = new ArrayList<EClass>();
				for (EClass superclass : ((EClass) classifier).getESuperTypes()) {
					superClasses.add(superclass);
				}

				reverse_inheritances.put((EClass) classifier, superClasses);

				for (EReference reference : ((EClass) classifier).getEAllReferences()) {
					if (!((EClass) classifier).getName().equals(XMICONTAINER)) {
						associations.add(reference);
					}
				}
			} else {
				if (classifier instanceof EEnum) {
					enumerations.add((EEnum) classifier);
				}
			}
		}
		inheritances = reverse(reverse_inheritances, classes);
	}

	/**
	 * Generates a .owl representation of the axioms created
	 * 
	 * @param name
	 *            The path to the file that must be created
	 * @throws OWLOntologyStorageException
	 * @throws ConsistencyCheckerGenericException
	 */
	public void save(String name, OWLOntology ontology)
			throws OWLOntologyStorageException, ConsistencyCheckerGenericException {
		if (ontology == null) {
			throw new ConsistencyCheckerGenericException(ERR_SAVE_NULL_ONTOLOGY);
		}
		// URI uri = URI.createURI("");
		// URI resolved = CommonPlugin.resolve(uri);
		// URI deres = URI.createFileURI(name).deresolve(resolved);
		File file = new File(name);
		java.net.URI u = file.toURI();
		ontologyManager_.saveOntology(ontology, IRI.create(u.toString()));
	}

	/**
	 * 
	 * @param model
	 *            String with the path to the Ecore model
	 * @return Returns the root EPackage of the Ecore model
	 */
	private EPackageImpl load(String model) {
		org.eclipse.emf.ecore.impl.EcorePackageImpl.init();

		ResourceSet resSet = new ResourceSetImpl();
		resSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put(ECORE_EXTENSION,
				new XMIResourceFactoryImpl());

		URI uri = URI.createURI("");
		URI resolved = CommonPlugin.resolve(uri);
		URI deres = URI.createFileURI(model).deresolve(resolved);
		Resource resource = resSet.getResource(deres, true);
		return (EPackageImpl) resource.getContents().get(0);
	}

	/**
	 * Checks if the Ecore model is wellFormed according to a set of rules.
	 * 
	 * @return Returns a list of formation errors and if/how they were recovered
	 * @throws ConsistencyCheckerGenericException
	 */
	protected ArrayList<String> isModelWellFormed() throws ConsistencyCheckerGenericException {
		int classCounter = 0;
		int attrCounter = 0;
		int methCounter = 0;
		int assocCounter = 0;
		ArrayList<String> errorsList = new ArrayList<String>();

		for (EClass classe : classes) {

			// Assures that every class has a name.
			if (classe.getName() == null || classe.getName().equals(SPACE)
					|| classe.getName().equals(Constants.EMPTY_STRING) || classe.getName().equals(NULL)) {
				classe.setName(CLASS_POSFIX + UNDERSCORE + classCounter);
				errorsList.add(String.format(ILL_FORMED_NAMELESS_CLASS_RECOVERED_ERROR,
						CLASS_POSFIX + UNDERSCORE + classCounter));
				classCounter++;
			}
			classe.setName(classe.getName().replaceAll(SPACE, Constants.EMPTY_STRING));

			for (EAttribute attribute : classe.getEAllAttributes()) {
				// Assures that every attribute has a name.
				if (attribute.getName() == null || attribute.getName().equals(SPACE)
						|| attribute.getName().equals(Constants.EMPTY_STRING) || attribute.getName().equals(NULL)) {
					attribute.setName(ATTRIBUTE_POSFIX + UNDERSCORE + attrCounter);
					errorsList.add(String.format(ILL_FORMED_NAMELESS_ATTR_RECOVERED_ERROR,
							ATTRIBUTE_POSFIX + UNDERSCORE + attrCounter));
					attrCounter++;
				}
				// Assures that every attribute has a type
				if (attribute.getEType() == null) {
					throw new ConsistencyCheckerGenericException(ILL_FORMED_TYPELESS_ATTR_EXCEPTION);
				}
				attribute.setName(attribute.getName().replaceAll(SPACE, Constants.EMPTY_STRING));
			}

			for (EOperation method : classe.getEAllOperations()) {
				// Assures that every method has a name.
				if (method.getName() == null || method.getName().equals(SPACE)
						|| method.getName().equals(Constants.EMPTY_STRING) || method.getName().equals(NULL)) {
					method.setName(METHOD_POSFIX + UNDERSCORE + methCounter);
					errorsList.add(String.format(ILL_FORMED_NAMELESS_METHOD_RECOVERED_ERROR,
							METHOD_POSFIX + UNDERSCORE + methCounter));
					methCounter++;
				}
				// Assures that every method has a type
				if (method.getEType() == null) {
					throw new ConsistencyCheckerGenericException(ILL_FORMED_TYPELESS_METHOD_PARAMETER_EXCEPTION);
				}

				for (EParameter eParameter : method.getEParameters()) {
					if (eParameter.getEType() == null) {
						throw new ConsistencyCheckerGenericException(ILL_FORMED_TYPELESS_METHOD_PARAMETER_EXCEPTION);
					}
				}
				method.setName(method.getName().replaceAll(SPACE, Constants.EMPTY_STRING));
			}
		}

		for (EReference association : associations) {
			if (association.getName() == null || association.getName().equals(Constants.EMPTY_STRING)
					|| association.getName().equals(NULL)) {
				association.setName(ASSOCIATION_POSFIX + UNDERSCORE + assocCounter);
				errorsList.add(String.format(ILL_FORMED_NAMELESS_ASSOCIATION_RECOVERED_ERROR,
						ASSOCIATION_POSFIX + UNDERSCORE + assocCounter));
				assocCounter++;
			}
			if (association.getEOpposite() == null) {
				throw new ConsistencyCheckerGenericException(
						String.format(ILL_FORMED_ASSOCIATIONEND_NO_OPOSITE, association.getName()));
			}
			if (association.getUpperBound() == 0) {
				throw new ConsistencyCheckerGenericException(
						String.format(ILL_FORMED_ASSOCIATIONEND_MULTIPLICITY_ERROR, association.getName()));
			}
			if (association.getUpperBound() > 0 && association.getLowerBound() > 0) {
				if (association.getUpperBound() < association.getLowerBound()) {
					throw new ConsistencyCheckerGenericException(
							String.format(ILL_FORMED_ASSOCIATIONEND_MULTIPLICITY_ERROR, association.getName()));
				}
			}
			if (association.getLowerBound() < 0) {
				throw new ConsistencyCheckerGenericException(
						String.format(ILL_FORMED_ASSOCIATIONEND_MULTIPLICITY_ERROR, association.getName()));
			}
			if (association.getUpperBound() < -1) {
				throw new ConsistencyCheckerGenericException(
						String.format(ILL_FORMED_ASSOCIATIONEND_MULTIPLICITY_ERROR, association.getName()));
			}
			if (association.getUpperBound() == -1 && association.getLowerBound() < 0) {
				throw new ConsistencyCheckerGenericException(
						String.format(ILL_FORMED_ASSOCIATIONEND_MULTIPLICITY_ERROR, association.getName()));
			}
			association.setName(association.getName().replaceAll(SPACE, Constants.EMPTY_STRING));
		}

		return errorsList;
	}

	/**
	 * Transforms an Ecore model to its representation in OWLAxioms
	 * 
	 * @param input_model
	 *            String with the path to the Ecore model to be transformed in
	 *            axioms
	 * @return Return a OWLOntology with the axioms that represents the Ecore
	 *         model
	 * @throws ConsistencyCheckerGenericException
	 * @throws OWLOntologyCreationException
	 * @throws ParserException
	 */
	public OWLOntology processAndCreateOntology(String input_model, StringBuilder log)
			throws ConsistencyCheckerGenericException, OWLOntologyCreationException, ParserException {
		log.append(LOG_PARSING_MODEL);
		parse(input_model, log);
		log.append(LOG_PARSED_MODEL);
		ArrayList<String> errorsList;
		OWLOntology ret = null;
		log.append(LOG_CHECKING_WELL_FORMEDNESS);
		errorsList = isModelWellFormed();
		log.append(LOG_CHECKED_WELL_FORMEDNESS);
		if (errorsList.size() > 0) {
			log.append(LOG_PRINTING_ERRORS);
			Main.printMessageModelIllFormed(errorsList);
			log.append(LOG_PRINTED_ERRORS);
		}
		log.append(LOG_CREATING_ONTOLOGY);
		ret = createOntology(log);
		log.append(LOG_CREATED_ONTOLOGY);
		return ret;
	}

	/**
	 * Transforms an Ecore model to its representation in OWLAxioms
	 * 
	 * @param input_model
	 *            Root EPackage of the Ecore model to be transformed in axioms
	 * @return Return a OWLOntology with the axioms that represents the Ecore
	 *         model
	 * @throws ConsistencyCheckerGenericException
	 * @throws ParserException
	 * @throws OWLOntologyCreationException
	 */
	public OWLOntology processAndCreateOntology(EPackage input_model, StringBuilder log)
			throws ConsistencyCheckerGenericException, ParserException, OWLOntologyCreationException {
		parse(input_model, log);
		ArrayList<String> errorsList;
		OWLOntology ret = null;
		errorsList = isModelWellFormed();
		if (errorsList.size() > 0) {
			Main.printMessageModelIllFormed(errorsList);
		}
		ret = createOntology(log);
		return ret;
		// return createOntology();
	}

	/**
	 * Transforms an Ecore model to its representation in OWLAxioms
	 * 
	 * @return Return a OWLOntology with the axioms that represents the Ecore
	 *         model
	 * @throws ConsistencyCheckerGenericException
	 * @throws OWLOntologyCreationException
	 * @throws ParserException
	 */
	protected OWLOntology createOntology(StringBuilder log)
			throws ConsistencyCheckerGenericException, OWLOntologyCreationException, ParserException {
		HashMap<EReference, Boolean> references = new HashMap<EReference, Boolean>();
		for (EClass classe : classes) {
			log.append(String.format(LOG_CHECKING_ECLASS, classe.getName()));

			log.append(String.format(LOG_CHECKING_ECLASS_ATTRIBUTES, classe.getName()));
			for (EAttribute attribute : classe.getEAllAttributes()) {
				if (checkOWLDataType(attribute.getEAttributeType().getName())) {
					log.append(String.format(LOG_CHECKING_ECLASS_ATTRIBUTES_DATA_TYPE, attribute.getName(),
							classe.getName()));
					makeAttributeAxioms(classe, attribute);
				} else {
					log.append(String.format(LOG_CHECKING_ECLASS_ATTRIBUTES_NOT_DATA_TYPE, attribute.getName(),
							classe.getName()));
					makeAttributeAxiomsClass(classe, attribute);
				}
				log.append(
						String.format(LOG_ATTRIBUTE_AXIOM_GENERATION_FINISHED, attribute.getName(), classe.getName()));
			}
			log.append(String.format(LOG_CHECKED_ECLASS_ATTRIBUTES, classe.getName()));

			log.append(String.format(LOG_CHECKING_ECLASS_METHODS, classe.getName()));
			for (EOperation method : classe.getEAllOperations()) {
				log.append(String.format(LOG_GENERATING_ECLASS_METHODS_AXIOMS, method.getName(), classe.getName()));
				makeOperationAxioms(classe, method);
				log.append(String.format(LOG_GENERATED_ECLASS_METHODS_AXIOMS, method.getName(), classe.getName()));
			}
			log.append(String.format(LOG_CHECKED_ECLASS_METHODS, classe.getName()));

			log.append(String.format(LOG_CHECKING_ANNOTATIONS, classe.getName()));
			for (EAnnotation ant : classe.getEAnnotations()) {
				if (ant.getSource().equals(PIVOT_URL)) {
					log.append(
							String.format(LOG_CHECKING_ECLASS_INVARIANTS, classe.getName(), ant.getDetails().size()));
					for (int i = 0; i < ant.getDetails().size(); i++) {
						log.append(String.format(LOG_CREATING_AXIOMS_INVARIANT, i, classe.getName()));
						makeInvariantAxioms(classe, ant.getDetails().get(i));
						log.append(String.format(LOG_CREATED_AXIOMS_INVARIANT, i, classe.getName()));
					}
				}
			}
			log.append(LOG_CHECKED_ANNOTATIONS);

			log.append(String.format(LOG_CREATING_AXIOMS_INHERITANCE, classe.getName()));
			makeGeneralizationAxiom(inheritances, classe);
			log.append(String.format(LOG_CREATED_AXIOMS_INHERITANCE, classe.getName()));

			log.append(String.format(LOG_CHECKED_ECLASS, classe.getName()));
		}

		for (EReference association : associations) {
			if (references.get(association) == null) {
				log.append(String.format(LOG_CREATING_AXIOMS_EREFERENCE, association.getName(),
						association.getEOpposite().getName()));
				makeAssociatonAxiom(association, association.getEOpposite());
				references.put(association, Boolean.TRUE);
				references.put(association.getEOpposite(), Boolean.TRUE);
				log.append(String.format(LOG_CREATED_AXIOMS_EREFERENCE, association.getName(),
						association.getEOpposite().getName()));
			}
		}
		log.append(LOG_GATHERING_AXIOMS);
		OWLOntology ontology_ = ontologyManager_.createOntology(ontologyIRI_);
		List<OWLOntologyChange> ontologyResulted = ontologyManager_.addAxioms(ontology_, axiomList_);
		ontologyManager_.applyChanges(ontologyResulted);
		log.append(LOG_GATHERED_AXIOMS);
		return ontology_;
	}

	protected void makeInvariantAxioms(EClass cls, Entry<String, String> par) throws ParserException {
		OCL<EPackage, EClassifier, EOperation, EStructuralFeature, EEnumLiteral, EParameter, EObject, CallOperationAction, SendSignalAction, Constraint, EClass, EObject> ocl = OCL
				.newInstance(EcoreEnvironmentFactory.INSTANCE);
		OCLHelper<EClassifier, EOperation, EStructuralFeature, Constraint> helper = ocl.createOCLHelper();

		helper.setContext(cls);
		String expOriginal = par.getValue();
		OCLExpression<EClassifier> invariant = helper.createQuery(expOriginal);
		ECCAbstractVisitor visit = new ECCAbstractVisitor(cls.getName(), ontologyIRI_, PACKAGE_PREFIX);
		invariant.accept(visit);
		while (!expOriginal.equals(visit.mainSt.print())) {
			expOriginal = visit.mainSt.print();
			invariant = helper.createQuery(expOriginal);
			visit = new ECCAbstractVisitor(cls.getName(), ontologyIRI_, PACKAGE_PREFIX);
			invariant.accept(visit);
		}
		OWLClassExpression invInDl = visit.mainSt.resolveStack();
		OWLClass alfa = owlDataFactory_.getOWLClass(IRI
				// .create(ontologyIRI_ + POUND_SIGN
				// + PACKAGE_PREFIX
				// + cls.getName()
				// + CLASS_POSFIX));
				.create(String.format(CLASS_NAME_BUILDER, cls.getName())));
		OWLAxiom sub = owlDataFactory_.getOWLSubClassOfAxiom(alfa, invInDl);
		axiomList_.add(sub);
		// log.append(String.format(LOG_CHECKED_ANNOTATIONS,cls.getName()));
		// log.append(String.format(LOG_ADDED_CLASS_IN_POOL,cls.getName()));

	}

	/**
	 * Inverts a map that maps the sons into fathers, to a map that maps fathers
	 * into sons
	 * 
	 * @param relatives
	 *            Original map
	 * @param classes
	 *            All classes in the model
	 * @return Returns an reversed Map
	 */
	protected static HashMap<EClass, ArrayList<EClass>> reverse(HashMap<EClass, ArrayList<EClass>> relatives,
			ArrayList<EClass> classes) {
		HashMap<EClass, ArrayList<EClass>> paiFilhos = new HashMap<EClass, ArrayList<EClass>>();
		for (EClass cls : classes) {
			paiFilhos.put(cls, new ArrayList<EClass>());
		}
		for (EClass cls : classes) {
			for (EClass superClass : relatives.get(cls)) {
				paiFilhos.get(superClass).add(cls);
			}
		}
		return paiFilhos;

	}

	protected OWLClass createOWLEnum(EEnum en) {
		HashSet<OWLIndividual> owlindividuals = new HashSet<OWLIndividual>();
		for (EEnumLiteral item : en.getELiterals()) {
			OWLIndividual i = owlDataFactory_.getOWLNamedIndividual(IRI.create(ontologyIRI_ + POUND_SIGN
					+ PACKAGE_PREFIX + item.getName().replaceAll(SPACE, Constants.EMPTY_STRING) + INDIVIDUAL_POSFIX));
			owlindividuals.add(i);
		}
		OWLClass owlEn = owlDataFactory_.getOWLClass(IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
				+ en.getName().replaceAll(SPACE, Constants.EMPTY_STRING) + ENUMERATION_POSFIX));
		OWLObjectOneOf enumeration = owlDataFactory_.getOWLObjectOneOf(owlindividuals);
		OWLAxiom c = owlDataFactory_.getOWLEquivalentClassesAxiom(owlEn, enumeration);
		axiomList_.add(c);
		return owlEn;
	}

	protected boolean checkOWLDataType(String typeName) {
		if (typeName.equals("EInt") || typeName.equals("EFloat") || typeName.equals("EDouble")
				|| typeName.equals("OWLInteger") || typeName.equals("OWLint") || typeName.equals("OWLfloat")
				|| typeName.equals("EBoolean") || typeName.equals("OWLdouble") || typeName.equals("OWLboolean")) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * 
	 * An UML class C is represented by an atomic concept C. Each attribute a of
	 * type T for class C is represented by an atomic role a, together with an
	 * inclusion assertion encoding the typing of the attribute a for the class
	 * C:
	 * 
	 * C \(\sqsubseteq \forall a.\top\)
	 * 
	 * We formalize the multiplicity [i..j ] of attribute a as
	 * 
	 * C \sqsubseteq (\geq i a.\top) \sqcap (\leq j a.\top)
	 * 
	 * expressing that for each instance of the concept C there are at least i
	 * and at most j role fillers for role a. For attributes with multiplicity
	 * [0..���] we omit the whole assertion, and when the multiplicity is
	 * missing (i.e., [1..1] is assumed) the above assertion becomes:
	 * 
	 * C \sqsubseteq \exists a.\top \sqcap (\leq 1 a.\top)
	 * 
	 */
	protected void makeAttributeAxioms(EClass cls, EAttribute attribute) {
		OWLClass owlAttributeTypeCls = null;
		OWLDataProperty owlAttribute = null;
		OWLObjectProperty owlAttObj = null;

		OWLClass owlClass = owlDataFactory_.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, cls.getName())));
		// create(ontologyIRI_+ POUND_SIGN + PACKAGE_PREFIX + cls.getName() +
		// CLASS_POSFIX));
		boolean isBuiltIn = true;
		OWLDatatype owlType = createDataType(attribute.getEAttributeType().getName());
		if (owlType == null) {
			isBuiltIn = false;
			owlAttributeTypeCls = owlDataFactory_.getOWLClass(
					IRI.create(String.format(CLASS_NAME_BUILDER, attribute.getEAttributeType().getName())));
			// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
			// + attribute.getEAttributeType().getName()
			// + CLASS_POSFIX));
			owlAttObj = owlDataFactory_.getOWLObjectProperty(IRI.create(
					ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + cls.getName() + attribute.getName() + ROLE_POSFIX));
		} else {

			owlAttribute = owlDataFactory_.getOWLDataProperty(IRI.create(
					ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + cls.getName() + attribute.getName() + ROLE_POSFIX));
		}

		OWLClassExpression owlAllAttofType = null;
		if (isBuiltIn) {
			owlAllAttofType = owlDataFactory_.getOWLDataAllValuesFrom(owlAttribute, owlType);
		} else {
			owlAllAttofType = owlDataFactory_.getOWLObjectAllValuesFrom(owlAttObj, owlAttributeTypeCls);
		}
		OWLAxiom subsumsForAll = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, owlAllAttofType);
		axiomList_.add(subsumsForAll);

		OWLAxiom subsumsCardinalities;

		if (attribute.getLowerBound() == 0 || attribute.getUpperBound() == -1) {
			if (attribute.getLowerBound() != 0) {
				OWLClassExpression owlMin = null;
				if (isBuiltIn) {
					owlMin = owlDataFactory_.getOWLDataMinCardinality(attribute.getLowerBound(), owlAttribute);
				} else {
					owlMin = owlDataFactory_.getOWLObjectMinCardinality(attribute.getLowerBound(), owlAttObj);
				}
				subsumsCardinalities = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, owlMin);
				axiomList_.add(subsumsCardinalities);
			}
			if (attribute.getUpperBound() != -1) {
				OWLClassExpression owlMax = null;
				if (isBuiltIn) {
					owlMax = owlDataFactory_.getOWLDataMaxCardinality(attribute.getUpperBound(), owlAttribute);
				} else {
					owlMax = owlDataFactory_.getOWLObjectMaxCardinality(attribute.getUpperBound(), owlAttObj);
				}
				subsumsCardinalities = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, owlMax);
				axiomList_.add(subsumsCardinalities);
			}
		} else {
			OWLClassExpression owlMax = null;
			if (isBuiltIn) {
				owlMax = owlDataFactory_.getOWLDataMaxCardinality(attribute.getUpperBound(), owlAttribute);
			} else {
				owlMax = owlDataFactory_.getOWLObjectMaxCardinality(attribute.getUpperBound(), owlAttObj);
			}

			OWLClassExpression intersec;
			if (attribute.getLowerBound() == 1 && attribute.getUpperBound() == 1) {
				OWLClassExpression owlExistsAttofType = null;
				if (isBuiltIn) {
					owlExistsAttofType = owlDataFactory_.getOWLDataSomeValuesFrom(owlAttribute, owlType);
				} else {
					owlExistsAttofType = owlDataFactory_.getOWLObjectSomeValuesFrom(owlAttObj, owlAttributeTypeCls);
				}

				intersec = owlDataFactory_.getOWLObjectIntersectionOf(owlExistsAttofType, owlMax);
			} else {
				OWLClassExpression owlMin = null;
				if (isBuiltIn) {
					owlMin = owlDataFactory_.getOWLDataMinCardinality(attribute.getUpperBound(), owlAttribute);
				} else {
					owlMin = owlDataFactory_.getOWLObjectMinCardinality(attribute.getUpperBound(), owlAttObj);
				}
				intersec = owlDataFactory_.getOWLObjectIntersectionOf(owlMin, owlMax);
			}
			subsumsCardinalities = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, intersec);
			axiomList_.add(subsumsCardinalities);
		}
	}

	/**
	 * 
	 * An UML class C is represented by an atomic concept C. Each attribute a of
	 * type T for class C is represented by an atomic role a, together with an
	 * inclusion assertion encoding the typing of the attribute a for the class
	 * C:
	 * 
	 * C \(\sqsubseteq \forall a.\top\)
	 * 
	 * We formalize the multiplicity [i..j ] of attribute a as
	 * 
	 * C \sqsubseteq (\geq i a.\top) \sqcap (\leq j a.\top)
	 * 
	 * expressing that for each instance of the concept C there are at least i
	 * and at most j role fillers for role a. For attributes with multiplicity
	 * [0..���] we omit the whole assertion, and when the multiplicity is
	 * missing (i.e., [1..1] is assumed) the above assertion becomes:
	 * 
	 * C \sqsubseteq \exists a.\top \sqcap (\leq 1 a.\top)
	 * 
	 */
	protected void makeAttributeAxiomsClass(EClass cls, EAttribute attribute) {
		OWLClass owlClass = owlDataFactory_.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, cls.getName())));
		// .create(ontologyIRI_
		// + POUND_SIGN + PACKAGE_PREFIX + cls.getName() + CLASS_POSFIX));

		OWLClass owlAttType;
		if (attribute.getEAttributeType() instanceof EEnum) {
			owlAttType = createOWLEnum((EEnum) attribute.getEAttributeType());
		} else {
			owlAttType = owlDataFactory_.getOWLClass(
					IRI.create(String.format(CLASS_NAME_BUILDER, attribute.getEAttributeType().getName())));
			// .create(ontologyIRI_
			// + POUND_SIGN + PACKAGE_PREFIX
			// + attribute.getEAttributeType().getName() + CLASS_POSFIX));
		}
		OWLObjectProperty owlAttribute = owlDataFactory_.getOWLObjectProperty(IRI.create(
				ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + cls.getName() + attribute.getName() + ROLE_POSFIX));

		OWLClassExpression owlAllAttofType = owlDataFactory_.getOWLObjectAllValuesFrom(owlAttribute, owlAttType);

		OWLAxiom subsumsForAll = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, owlAllAttofType);

		axiomList_.add(subsumsForAll);

		OWLAxiom subsumsCardinalities;

		if (attribute.getLowerBound() == 0 || attribute.getUpperBound() == -1) {
			if (attribute.getLowerBound() != 0) {
				OWLClassExpression owlMin = owlDataFactory_.getOWLObjectMinCardinality(attribute.getLowerBound(),
						owlAttribute);
				subsumsCardinalities = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, owlMin);
				axiomList_.add(subsumsCardinalities);
			}
			if (attribute.getUpperBound() != -1) {
				OWLClassExpression owlMax = owlDataFactory_.getOWLObjectMaxCardinality(attribute.getUpperBound(),
						owlAttribute);
				subsumsCardinalities = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, owlMax);
				axiomList_.add(subsumsCardinalities);
			}
		} else {
			OWLClassExpression owlMax = owlDataFactory_.getOWLObjectMaxCardinality(attribute.getUpperBound(),
					owlAttribute);
			OWLClassExpression intersec;
			if (attribute.getLowerBound() == 1 && attribute.getUpperBound() == 1) {
				OWLClassExpression owlExistsAttofType = owlDataFactory_.getOWLObjectSomeValuesFrom(owlAttribute,
						owlAttType);
				intersec = owlDataFactory_.getOWLObjectIntersectionOf(owlExistsAttofType, owlMax);
			} else {
				OWLClassExpression owlMin = owlDataFactory_.getOWLObjectMinCardinality(attribute.getUpperBound(),
						owlAttribute);
				intersec = owlDataFactory_.getOWLObjectIntersectionOf(owlMin, owlMax);
			}
			subsumsCardinalities = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, intersec);
			axiomList_.add(subsumsCardinalities);
		}
	}

	/**
	 * An operation f() : R without parameters for class C is modeled directly
	 * as a (binary) role R_{f()} , for which the following assertion holds:
	 * 
	 * C \sqsubseteq \forall R_{f()}.R \sqcap (\leq 1 R_{f()}.\top)
	 * 
	 * Instead, an operation with one or more parameters f (P1, . . . , Pm) : R
	 * of class C, which formally corresponds to an (m + 2)-ary relation that is
	 * functional on the last component, cannot be directly expressed in ALCQI.
	 * Therefore, we make use of reification, and introduce an atomic concept Cf
	 * (P1,...,Pm), m + 2 ALCQI roles r1, . . . , rm+2 and the following
	 * assertions, which type the input parameters and the return value:
	 * 
	 * 
	 * C_{f(P_1,...P_m)} \sqsubseteq \exists r_1.\top \sqcap (\leq 1 r_1.\top)
	 * \sqcap ... ... ... \exists r_{m+1}.\top \sqcap (\leq 1 r_{m+1}.\top)
	 * \sqcap C_{f(P_1,...P_m)} \sqsubseteq \forall r_2 .P_1 \sqcap ... \sqcap
	 * \forall r_{m+1} . P_m C \sqsubseteq \forall r^{-}_1.(C_{f(P_1,...P_m)}
	 * \Rightarrow \forall r_{m+2}.R
	 * 
	 * The first assertion states that each instance of C_{f(P1,...,Pm)},
	 * representing a tuple, correctly is connected to exactly one object for
	 * each of the roles r_1,...,r_{m+1}. Instead, note that in general there
	 * may be two instances of C_{f(P1 ,...,Pm )} representing the same tuple.
	 * However, this cannot be the case in a tree-like model (cf. tree-model
	 * property). The other two assertions impose the correct typing of the
	 * parameters, depending only on the name of the operation, and of the
	 * return value, depending also on the class.
	 */
	protected void makeOperationAxioms(EClass cls, EOperation method) {
		if (method.getEParameters().size() == 0) {
			OWLDatatype owlReturnTypeDataType = null;
			OWLClass owlReturnTypeClass = null;
			boolean isDataType = false;
			OWLClass owlClass = owlDataFactory_
					.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, cls.getName())));
			// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
			// + cls.getName() + CLASS_POSFIX));
			if (checkOWLDataType(method.getEType().getName())) {
				owlReturnTypeDataType = createDataType(method.getEType().getName());
				isDataType = true;
			} else {
				owlReturnTypeClass = owlDataFactory_
						.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, method.getEType().getName())));
				// .create(ontologyIRI_ + POUND_SIGN
				// + PACKAGE_PREFIX + method.getEType().getName() +
				// CLASS_POSFIX));
				isDataType = false;
			}

			OWLClassExpression owlAllAttofType = null;
			OWLDataProperty owlReturnOperationDataType = null;
			OWLObjectProperty owlReturnOperationClass = null;
			OWLClassExpression owlMax = null;
			if (isDataType) {
				owlReturnOperationDataType = owlDataFactory_.getOWLDataProperty(
						IRI.create(ontologyIRI_ + POUND_SIGN + RETURN + PACKAGE_PREFIX + cls.getName()
								+ method.getName() + method.getEType().getName() + RETURN + ROLE_POSFIX));
				owlAllAttofType = owlDataFactory_.getOWLDataAllValuesFrom(owlReturnOperationDataType,
						owlReturnTypeDataType);
				owlMax = owlDataFactory_.getOWLDataMaxCardinality(1, owlReturnOperationDataType);
			} else {
				owlReturnOperationClass = owlDataFactory_.getOWLObjectProperty(
						IRI.create(ontologyIRI_ + POUND_SIGN + RETURN + PACKAGE_PREFIX + cls.getName()
								+ method.getName() + method.getEType().getName() + RETURN + ROLE_POSFIX));
				owlAllAttofType = owlDataFactory_.getOWLObjectAllValuesFrom(owlReturnOperationClass,
						owlReturnTypeClass);
				owlMax = owlDataFactory_.getOWLObjectMaxCardinality(1, owlReturnOperationClass);
			}

			OWLClassExpression intersec = owlDataFactory_.getOWLObjectIntersectionOf(owlAllAttofType, owlMax);
			OWLAxiom subsumsIntersec = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, intersec);
			axiomList_.add(subsumsIntersec);
		} else {
			OWLClass operationClass = owlDataFactory_.getOWLClass(IRI.create(
					String.format(CLASS_NAME_BUILDER, cls.getName() + method.getName() + method.getEType().getName())));
			// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
			// + cls.getName() + method.getName()
			// + method.getEType().getName() + CLASS_POSFIX));
			Set<OWLClassExpression> elementsForIntersection = new HashSet<OWLClassExpression>();
			Set<OWLClassExpression> paramTypeForIntersection = new HashSet<OWLClassExpression>();

			OWLObjectProperty owlThis = owlDataFactory_.getOWLObjectProperty(IRI
					.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + cls.getName() + cls.getName() + ROLE_POSFIX));
			OWLClassExpression owlExistsThistofType = owlDataFactory_.getOWLObjectSomeValuesFrom(owlThis, thing);
			elementsForIntersection.add(owlExistsThistofType);
			OWLClassExpression owlMax = owlDataFactory_.getOWLObjectMaxCardinality(1, owlThis, thing);
			elementsForIntersection.add(owlMax);

			for (EParameter eParameter : method.getEParameters()) {
				OWLObjectProperty owlParam = owlDataFactory_.getOWLObjectProperty(IRI.create(ontologyIRI_ + POUND_SIGN
						+ PACKAGE_PREFIX + cls.getName() + method.getName() + eParameter.getName() + ROLE_POSFIX));
				OWLClassExpression owlExistsParamtofType = owlDataFactory_.getOWLObjectSomeValuesFrom(owlParam, thing);
				elementsForIntersection.add(owlExistsParamtofType);
				owlMax = owlDataFactory_.getOWLObjectMaxCardinality(1, owlParam, thing);
				elementsForIntersection.add(owlMax);

				OWLClass owlParamRet = owlDataFactory_.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER,
						cls.getName() + method.getName() + eParameter.getEType().getName())));
				// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
				// + cls.getName() + method.getName()
				// + eParameter.getEType().getName()
				// + CLASS_POSFIX));
				OWLClassExpression owlAllAttofType = owlDataFactory_.getOWLObjectAllValuesFrom(owlParam, owlParamRet);
				paramTypeForIntersection.add(owlAllAttofType);
			}
			OWLClassExpression intersec = owlDataFactory_.getOWLObjectIntersectionOf(elementsForIntersection);
			OWLAxiom subsumsIntersec = owlDataFactory_.getOWLSubClassOfAxiom(operationClass, intersec);
			axiomList_.add(subsumsIntersec);

			intersec = owlDataFactory_.getOWLObjectIntersectionOf(paramTypeForIntersection);
			subsumsIntersec = owlDataFactory_.getOWLSubClassOfAxiom(operationClass, intersec);
			axiomList_.add(subsumsIntersec);

			OWLClass owlMetRet = owlDataFactory_.getOWLClass(
					IRI.create(String.format(CLASS_NAME_BUILDER, cls.getName() + method.getEType().getName())));
			// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
			// + cls.getName() + method.getEType().getName()
			// + CLASS_POSFIX));
			OWLObjectProperty owlParam = owlDataFactory_.getOWLObjectProperty(IRI.create(ontologyIRI_ + POUND_SIGN
					+ PACKAGE_PREFIX + cls.getName() + method.getEType().getName() + ROLE_POSFIX));
			OWLClassExpression owlAllAttofType = owlDataFactory_.getOWLObjectAllValuesFrom(owlParam, owlMetRet);
			OWLClassExpression notCalva = owlDataFactory_.getOWLObjectComplementOf(operationClass);
			OWLClassExpression equivalentImplication = owlDataFactory_.getOWLObjectUnionOf(notCalva, owlAllAttofType);

			OWLObjectPropertyExpression inverseThis = owlDataFactory_.getOWLObjectInverseOf(owlThis);

			OWLClassExpression forAllInverse = owlDataFactory_.getOWLObjectAllValuesFrom(inverseThis,
					equivalentImplication);

			OWLClass owlClass = owlDataFactory_
					.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, cls.getName())));
			// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
			// + cls.getName() + CLASS_POSFIX));
			OWLAxiom subsumsImplies = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, forAllInverse);
			axiomList_.add(subsumsImplies);
		}
	}

	/**
	 * Each binary association (or aggregation) A between a class C_1 and a
	 * class C_2 is represented by the atomic role A, together with the
	 * inclusion assertion
	 * 
	 * \top \sqsubseteq \forall A.C_2 \sqcap \forallA^���.C_1
	 * 
	 * encoding the typing of A. The multiplicities of A are formalized by the
	 * assertions
	 * 
	 * C_1 \sqsubseteq (\geq n_l A.\top) \sqcap (\leq n_u A.\top) C_2
	 * \sqsubseteq (\geq m_l A^-.\top) \sqcap (\leq m_u A^-.\top)
	 * 
	 * 
	 * //NOTE: Even that n-ary associations and associations with association
	 * class are suported by D. Berardi et al. mapping, Ecore does not suport
	 * this constructions
	 * 
	 * Binary associations with association class, and n-ary (with n biggen than
	 * 2) associations, with or without association class, are modeled through
	 * reification. More precisely, each association A relating classes
	 * C_1,...,C_n is represented by an atomic concept A together with the
	 * inclusion assertion
	 * 
	 * A \sqsubseteq \exists r_1.C_1 \sqcap...\sqcap \exists r_n.C_n \sqcap
	 * (\leq 1 r_1) \sqcap ... (\leq 1 r_n)
	 * 
	 * If the association A has explicit role names in the UML class diagram,
	 * then r_1,...,r_n above are such names. Otherwise, they are arbitrary
	 * names used to denote the components of A. As we did for operations, we
	 * are not requiring that each instance of the concept A denotes a distinct
	 * tuple, but again this is the case in tree-like models. Multiplicities on
	 * binary associations with association class (see Fig. 4) are represented
	 * by
	 * 
	 * C_1 \sqsubseteq (\geq n_l r^{-}_1.A) \sqcap (\leq n_u r^{-}_1.A) C_2
	 * \sqsubseteq (\geq m_l r^{-}_2.A) \sqcap (\leq m_u r^{-}_2.A)
	 */
	protected void makeAssociatonAxiom(EReference associationLeft, EReference associationRight)
			throws ConsistencyCheckerGenericException {
		if (!(associationLeft.getEOpposite().equals(associationRight))) {
			throw new ConsistencyCheckerGenericException(ONTOLOGY_CREATOR_ASSOCIATION_ROLES_NOT_OPOSITE_ERROR);
		}

		OWLObjectProperty roleLeft = owlDataFactory_.getOWLObjectProperty(
				IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + associationRight.getEReferenceType().getName()
						+ associationLeft.getName() + associationLeft.getEReferenceType().getName() + ROLE_POSFIX));
		// OWLObjectProperty roleLeft = owlDataFactory_.getOWLObjectProperty(IRI
		// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
		// + associationLeft.getEReferenceType().getName()
		// + associationLeft.getName() + ROLE_POSFIX));
		OWLClass leftClass = owlDataFactory_.getOWLClass(
				IRI.create(String.format(CLASS_NAME_BUILDER, associationLeft.getEReferenceType().getName())));
		// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
		// + associationLeft.getEReferenceType().getName()
		// + CLASS_POSFIX));
		OWLClassExpression forallRoleLeftClass = owlDataFactory_.getOWLObjectAllValuesFrom(roleLeft, leftClass);
		OWLObjectProperty roleRight = owlDataFactory_.getOWLObjectProperty(
				IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + associationLeft.getEReferenceType().getName()
						+ associationRight.getName() + associationRight.getEReferenceType().getName() + ROLE_POSFIX));
		// OWLObjectProperty roleRight =
		// owlDataFactory_.getOWLObjectProperty(IRI
		// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
		// + associationRight.getEReferenceType().getName()
		// + associationRight.getName() + ROLE_POSFIX));
		OWLClass rightClass = owlDataFactory_.getOWLClass(
				IRI.create(String.format(CLASS_NAME_BUILDER, associationRight.getEReferenceType().getName())));
		// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
		// + associationRight.getEReferenceType().getName()
		// + CLASS_POSFIX));
		OWLClassExpression forallRoleRightClass = owlDataFactory_.getOWLObjectAllValuesFrom(roleRight, rightClass);

		OWLClassExpression inter = owlDataFactory_.getOWLObjectIntersectionOf(forallRoleLeftClass,
				forallRoleRightClass);
		OWLAxiom subClassAxiom = owlDataFactory_.getOWLSubClassOfAxiom(thing, inter);
		axiomList_.add(subClassAxiom);

		OWLAxiom rightEqualsLeftInverse = owlDataFactory_.getOWLInverseObjectPropertiesAxiom(roleLeft, roleRight);
		axiomList_.add(rightEqualsLeftInverse);

		OWLCardinalityRestriction<?, ?, ?> cardMinLeft = null;
		OWLCardinalityRestriction<?, ?, ?> cardMaxLeft = null;

		if ((associationRight.getLowerBound() > 0)) {
			cardMinLeft = owlDataFactory_.getOWLObjectMinCardinality(associationRight.getLowerBound(), roleRight);
		}
		if ((associationRight.getUpperBound() != -1)) {
			cardMaxLeft = owlDataFactory_.getOWLObjectMaxCardinality(associationRight.getUpperBound(), roleRight);
		}
		if (cardMaxLeft != null && cardMinLeft != null) {
			OWLClassExpression intersectionAxiomLeft = owlDataFactory_.getOWLObjectIntersectionOf(cardMinLeft,
					cardMaxLeft);
			OWLAxiom subsumbsIntersectionLeft = owlDataFactory_.getOWLSubClassOfAxiom(leftClass, intersectionAxiomLeft);
			axiomList_.add(subsumbsIntersectionLeft);
		} else {
			if (!(cardMaxLeft == null && cardMinLeft == null)) {
				if (cardMaxLeft == null) {
					OWLAxiom subsumbsMinLeft = owlDataFactory_.getOWLSubClassOfAxiom(leftClass, cardMinLeft);
					axiomList_.add(subsumbsMinLeft);
				} else {
					OWLAxiom subsumbsMaxLeft = owlDataFactory_.getOWLSubClassOfAxiom(leftClass, cardMaxLeft);
					axiomList_.add(subsumbsMaxLeft);
				}
			}
		}

		OWLCardinalityRestriction<?, ?, ?> cardMinRight = null;
		OWLCardinalityRestriction<?, ?, ?> cardMaxRight = null;

		if ((associationLeft.getLowerBound() > 0)) {
			cardMinRight = owlDataFactory_.getOWLObjectMinCardinality(associationLeft.getLowerBound(), roleLeft);
		}
		if ((associationLeft.getUpperBound() != -1)) {
			cardMaxRight = owlDataFactory_.getOWLObjectMaxCardinality(associationLeft.getUpperBound(), roleLeft);
		}
		if (cardMaxRight != null && cardMinRight != null) {
			OWLClassExpression intersectionAxiomRight = owlDataFactory_.getOWLObjectIntersectionOf(cardMinRight,
					cardMaxRight);
			OWLAxiom subsumbsIntersectionRight = owlDataFactory_.getOWLSubClassOfAxiom(rightClass,
					intersectionAxiomRight);
			axiomList_.add(subsumbsIntersectionRight);
		} else {
			if (!(cardMaxRight == null && cardMinRight == null)) {
				if (cardMaxRight == null) {
					OWLAxiom subsumbsMinRight = owlDataFactory_.getOWLSubClassOfAxiom(rightClass, cardMinRight);
					axiomList_.add(subsumbsMinRight);
				} else {
					OWLAxiom subsumbsMaxRight = owlDataFactory_.getOWLSubClassOfAxiom(rightClass, cardMaxRight);
					axiomList_.add(subsumbsMaxRight);
				}
			}
		}
	}

	/**
	 * In this implementation all inheritances are interpreted as complete and
	 * disjoint
	 * 
	 * Generalizations between classes, and disjointness and covering
	 * constraints on hierar chies are expressed in ALCQI as they are in
	 * DLR_{ifd}. In particular, a generalization between a class C and its
	 * child class C_1 can be represented using the ALCQI inclusion assertion
	 * C_1 \sqsubseteq C. A class hierarchy as the one in Fig. 9 can be
	 * represented by the assertions C_1 \sqsubseteq C,..., C_n \sqsubseteq C. A
	 * disjointness constraint among classes C_1,..., C_n can be modeled as C_i
	 * \sqsubseteq \sqcap^{n}_{j=i+1} \negC_j, with 1 \leq i \leq n-1, while a
	 * covering constraint can be expressed as C \sqsubseteq \sqcup^{n}_{i=1}
	 * C_i.
	 */
	protected void makeGeneralizationAxiom(HashMap<EClass, ArrayList<EClass>> inheritances, EClass father) {
		List<EClass> sonsList = inheritances.get(father);
		if (sonsList.size() > 0) {

			// Set<OWLClass> subClasses = new HashSet<OWLClass>();
			OWLClass fatherowl = owlDataFactory_
					.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, father.getName())));
			// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
			// + father.getName() + CLASS_POSFIX));
			for (EClass son : sonsList) {
				OWLClass owlSon = owlDataFactory_
						.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, son.getName())));
				// .create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
				// + son.getName() + CLASS_POSFIX));

				OWLAxiom myHierarchy = owlDataFactory_.getOWLSubClassOfAxiom(owlSon, fatherowl);
				axiomList_.add(myHierarchy);
				// subClasses.add(owlSon);
			}
			// ADICIONA A PROPRIEDADE DE ABSTRATO AO SUPERTIPO
			// if (father.getEAnnotations().size() > 0) {
			// if (father.getEAnnotations().get(0).getSource()
			// .contains("complete")) {
			// if (subClasses.size() > 0) {
			// OWLObjectUnionOf unionOfSubClasses = owlDataFactory_
			// .getOWLObjectUnionOf(subClasses);
			// OWLAxiom unionClassAxiom = owlDataFactory_
			// .getOWLSubClassOfAxiom(fatherowl,
			// unionOfSubClasses);
			// axiomList_.add(unionClassAxiom);
			// }
			// }
			// if (father.getEAnnotations().get(0).getSource()
			// .contains("disjoint")) {
			// OWLDisjointClassesAxiom dijointClassExpression = owlDataFactory_
			// .getOWLDisjointClassesAxiom(subClasses);
			// axiomList_.add(dijointClassExpression);
			// }
			// }
			// if (subClasses.size() > 0) {
			// if (subClasses.size() > 1) {
			// OWLDisjointClassesAxiom dijointClassExpression = owlDataFactory_
			// .getOWLDisjointClassesAxiom(subClasses);
			// axiomList_.add(dijointClassExpression);
			// }
			// OWLObjectUnionOf unionOfSubClasses = owlDataFactory_
			// .getOWLObjectUnionOf(subClasses);
			// OWLAxiom unionClassAxiom = owlDataFactory_
			// .getOWLSubClassOfAxiom(fatherowl, unionOfSubClasses);
			// axiomList_.add(unionClassAxiom);
			// }
		}
	}

	public OWLDatatype createDataType(String typeName) {
		OWLDatatype owlType;
		if (typeName.equals("EInt") || typeName.equals("OWLInteger") || typeName.equals("OWLint")) {
			owlType = owlDataFactory_.getIntegerOWLDatatype();
		} else {
			if (typeName.equals("EFloat") || typeName.equals("OWLfloat")) {
				owlType = owlDataFactory_.getFloatOWLDatatype();
			} else {
				if (typeName.equals("EDouble") || typeName.equals("OWLdouble")) {
					owlType = owlDataFactory_.getDoubleOWLDatatype();
				} else {
					if (typeName.equals("EBoolean") || typeName.equals("OWLboolean")) {
						owlType = owlDataFactory_.getBooleanOWLDatatype();
					} else {
						owlType = null;
						// owlType = owlDataFactory_.getOWLDatatype(IRI
						// .create(ontologyIRI_ + POUND_SIGN + typeName));
					}
				}
			}
		}
		return owlType;
	}
}
