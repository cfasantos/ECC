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
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EReference;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyChange;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import ecorexmiparser.EcoreXMIParser;
import ecorexmiparser.TLink;
import ecorexmiparser.TObject;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.1.0
 * @since 1.0.0
 * 
 */
public class ExtendedOntologyCreator extends OntologyCreator {
	
	protected static final String OBJECT_POSFIX = "object";
	
	// Variable used to implement the singleton design pattern
	private static ExtendedOntologyCreator instance;

	/**
	 * Standard Constructor. Calls the superclass constructor to instantiate
	 * attributes Used only internally. For external calls, the getInstance
	 * should be used to ensure the oneness of the instance.
	 * 
	 * @throws OWLOntologyCreationException
	 */
	private ExtendedOntologyCreator() throws OWLOntologyCreationException {
		super();
	}

	/**
	 * Implementation of the singleton design pattern. Use this method to get an instance of this class
	 * 
	 * @return returns the singleton instance
	 * @throws OWLOntologyCreationException
	 */
	public static ExtendedOntologyCreator getInstance() throws OWLOntologyCreationException {
		if (instance == null) {
			instance = new ExtendedOntologyCreator();
		}
		return instance;
	}

	/**
	 * 
	 * @param objectModelPath Full path for the .XMI representing the object model
	 * @return returns an OWLOntology representing the 
	 * @throws OWLOntologyCreationException
	 */
	public OWLOntology extendOntology(String objectModelPath) throws OWLOntologyCreationException {
		OWLOntologyManager ontologyManager_ = OWLManager.createOWLOntologyManager();
		//Instantiate the XMI parser providing the classes and associations retrieved from the Class Model
		EcoreXMIParser parser = new EcoreXMIParser(classes, associations, PACKAGE_PREFIX);
		//Parses the XMI File, creating and pools of objects and links
		parser.parse(objectModelPath);
		//Creates axioms representing the objects
		insertTypingAxioms(parser.getObjectPool());
		//Creates axioms representing the links
		insertLinksAxioms(parser.getObjectPool(), parser.getlinkPool());
		//Create the ontology containing the object model axioms
		OWLOntology ontology_ = ontologyManager_.createOntology(ontologyIRI_);
		//Adds the object model axioms to the previouly created metamodel axioms
		List<OWLOntologyChange> ontologyResulted = ontologyManager_.addAxioms(ontology_, axiomList_);
		ontologyManager_.applyChanges(ontologyResulted);
		//returns the extended ontology
		return ontology_;
	}

	public void insertTypingAxioms(Map<String, ArrayList<TObject>> objectPoolSimplified) {
		for (EClass cls : classes) {
			OWLClass owlClass = owlDataFactory_
					.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, cls.getName())));
			Set<OWLClass> objectBrothers = new HashSet<OWLClass>();
			for (TObject ob : objectPoolSimplified.get(cls.getName())) {
				OWLClass owlObject = owlDataFactory_.getOWLClass(
						IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + ob.getId() + OBJECT_POSFIX));
				objectBrothers.add(owlObject);
				OWLAxiom subsumsType = owlDataFactory_.getOWLSubClassOfAxiom(owlObject, owlClass);
				axiomList_.add(subsumsType);
			}
			if (objectBrothers.size() > 0) {
				if (objectBrothers.size() > 1) {
					OWLAxiom disjointness = owlDataFactory_.getOWLDisjointClassesAxiom(objectBrothers);
					axiomList_.add(disjointness);
				}
				OWLObjectUnionOf unionOfBrothers = owlDataFactory_.getOWLObjectUnionOf(objectBrothers);
				OWLAxiom subsumUnionAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, unionOfBrothers);
				axiomList_.add(subsumUnionAxiom);
			}
		}
	}

	public void insertLinksAxioms(Map<String, ArrayList<TObject>> objs,
			Map<String, HashMap<TObject, ArrayList<TLink>>> links) {
		for (EReference er : associations) {
			HashMap<String, Boolean> objectsInRelation = new HashMap<String, Boolean>();

			ArrayList<TObject> allObjectsFromSource = objs.get(er.getEOpposite().getEType().getName());
			for (TObject tObject : allObjectsFromSource) {
				objectsInRelation.put(tObject.getId(), false);
			}

			ArrayList<TObject> allObjectsFromTarget = objs.get(er.getEType().getName());

			Set<TObject> objectsInRelationSource = links.get(er.getEOpposite().getEType().getName() + er.getName())
					.keySet();
			for (TObject tObject : objectsInRelationSource) {
				objectsInRelation.put(tObject.getId(), true);
			}

			ArrayList<TObject> objectsFromSourceNotInRelation = new ArrayList<TObject>();
			for (TObject tObject : allObjectsFromSource) {
				if (!objectsInRelation.get(tObject.getId())) {
					objectsFromSourceNotInRelation.add(tObject);
				}
			}
			for (TObject tObjectSource : objectsFromSourceNotInRelation) {
				for (TObject tObjectTarget : allObjectsFromTarget) {
					OWLClass owlObjectSource = owlDataFactory_.getOWLClass(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + tObjectSource.getId() + OBJECT_POSFIX));
					OWLClass owlObjectTarget = owlDataFactory_.getOWLClass(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + tObjectTarget.getId() + OBJECT_POSFIX));
					OWLObjectProperty owlEr = owlDataFactory_.getOWLObjectProperty(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + er.getEOpposite().getEReferenceType().getName()
									+ er.getName() + er.getEReferenceType().getName() + ROLE_POSFIX));
					OWLObjectSomeValuesFrom exists = owlDataFactory_.getOWLObjectSomeValuesFrom(owlEr, owlObjectTarget);
					OWLObjectComplementOf complement = owlDataFactory_.getOWLObjectComplementOf(exists);
					OWLAxiom subsumAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlObjectSource, complement);
					axiomList_.add(subsumAxiom);
				}
			}
			HashMap<TObject, ArrayList<TLink>> assoc = links.get(er.getEOpposite().getEType().getName() + er.getName());
			for (TObject obj : objectsInRelationSource) {
				ArrayList<TObject> objectsRelated = new ArrayList<>();
				for (TLink link : assoc.get(obj)) {
					objectsRelated.add(objs.get(link.getType()).get(link.getPosition()));
					OWLClass owlObject = owlDataFactory_.getOWLClass(
							IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + obj.getId() + OBJECT_POSFIX));
					OWLObjectProperty owlEr = owlDataFactory_.getOWLObjectProperty(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + er.getEOpposite().getEReferenceType().getName()
									+ er.getName() + er.getEReferenceType().getName() + ROLE_POSFIX));
					OWLClass owlObjectTarget = owlDataFactory_
							.getOWLClass(IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
									+ objs.get(link.getType()).get(link.getPosition()).getId() + OBJECT_POSFIX));
					OWLObjectExactCardinality cardExaclty = owlDataFactory_.getOWLObjectExactCardinality(1, owlEr,
							owlObjectTarget);
					OWLAxiom subsumUnionAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlObject, cardExaclty);
					axiomList_.add(subsumUnionAxiom);
				}
				ArrayList<TObject> unrelatedObjects = new ArrayList<TObject>(allObjectsFromTarget);
				unrelatedObjects.removeAll(objectsRelated);
				for (TObject tObjectTarget : unrelatedObjects) {
					OWLClass owlObjectSource = owlDataFactory_.getOWLClass(
							IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + obj.getId() + OBJECT_POSFIX));
					OWLClass owlObjectTarget = owlDataFactory_.getOWLClass(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + tObjectTarget.getId() + OBJECT_POSFIX));
					OWLObjectProperty owlEr = owlDataFactory_.getOWLObjectProperty(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + er.getEOpposite().getEReferenceType().getName()
									+ er.getName() + er.getEReferenceType().getName() + ROLE_POSFIX));
					OWLObjectSomeValuesFrom exists = owlDataFactory_.getOWLObjectSomeValuesFrom(owlEr, owlObjectTarget);
					OWLObjectComplementOf complement = owlDataFactory_.getOWLObjectComplementOf(exists);
					OWLAxiom subsumAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlObjectSource, complement);
					axiomList_.add(subsumAxiom);
				}
			}
		}
	}

}
