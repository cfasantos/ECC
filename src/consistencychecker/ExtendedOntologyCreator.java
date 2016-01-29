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

	/**
	 * 
	 * @param objectPoolSimplified
	 * 			Pool of TObjects representing the objects in the object model.
	 * 			They're associated with their respective metaclass using the mapping.
	 */
	public void insertTypingAxioms(Map<String, ArrayList<TObject>> objectPoolSimplified) {
		//Runs through the classes list
		for (EClass currentClass : classes) {
			//Builds and OWLClas representing the class. (The name unicity theory assures that
			//we are referencing the same OWL Class created previously)
			OWLClass owlClass = owlDataFactory_
					.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, currentClass.getName())));
			//Creates a set to store all objects instances of the current class, here called siblingObjects
			Set<OWLClass> siblingObjects = new HashSet<OWLClass>();
			//Runs through the object List associated with the current class
			for (TObject currentObject : objectPoolSimplified.get(currentClass.getName())) {
				//Creates the OWLClass representing the object.
				OWLClass owlObject = owlDataFactory_.getOWLClass(
						IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentObject.getId() + OBJECT_POSFIX));
				//Adds the current object to the list of instances of the current class
				siblingObjects.add(owlObject);
				//Creates an axiom stating that the OWLClass representing the object
				//is an subclass of the OWLClass representing the class.
				OWLAxiom subsumsType = owlDataFactory_.getOWLSubClassOfAxiom(owlObject, owlClass);
				//Adds the axiom to the resulting axiom list
				axiomList_.add(subsumsType);
			}
			//Checks if there were any object associated with the current class
			if (siblingObjects.size() > 0) {
				//Checks if there were more than one object associated with the current class
				if (siblingObjects.size() > 1) {
					//If there were more than one object associated with the current class
					//Then, an disjointness axiom must exist, assuring that every OWLClass representing
					//an object instance of a class are disjoint to each other (Inheritance disjointness)
					OWLAxiom disjointness = owlDataFactory_.getOWLDisjointClassesAxiom(siblingObjects);
					//Adds the axiom to the resulting axiom list
					axiomList_.add(disjointness);
				}
				//If there were any object associated with the current class 
				//then, there must exist an axiom, assuring that the OWLClass representing 
				//the class is entirely represented by the OWLClass representing it's objects
				//assuring with this, that there are no objects not explicitly represented in the theory.
				//This axiom is necessary due the open world assumption in DL.
				
				//Creates an axiom representing the union of all objects instance of the current class
				OWLObjectUnionOf unionOfBrothers = owlDataFactory_.getOWLObjectUnionOf(siblingObjects);
				//Creates an axiom representing that the current class is a subset of the union of its objects
				OWLAxiom subsumUnionAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlClass, unionOfBrothers);
				//Adds the axiom to the resulting axiom list
				axiomList_.add(subsumUnionAxiom);
			}
		}
	}

	/**
	 * 
	 * @param objs
	 * 			Mapping relating a list of objects to its class
	 * @param links
	 * 			Mapping relating an association to a map of objects and links that implement such association
	 */
	public void insertLinksAxioms(Map<String, ArrayList<TObject>> objs,
			Map<String, HashMap<TObject, ArrayList<TLink>>> links) { 
		
		//Runs through the associations list
		for (EReference currentAssociation : associations) {
			
			//Stores all objects of the source type in a list
			ArrayList<TObject> allObjectsFromSource = objs.get(currentAssociation.getEOpposite().getEType().getName());
			
			//Stores all objects ids of the source type that implement the association in a list
			ArrayList<String> objectsIdsInAssociation = new ArrayList<String>();
			
			//Stores all objects from the source type with links that implement the current association
			//as being in the relation.
			Set<TObject> objectsInAssociationSource = links.get(currentAssociation.getEOpposite().getEType().getName() + currentAssociation.getName()).keySet();
			for (TObject tObject : objectsInAssociationSource) {
				objectsIdsInAssociation.add(tObject.getId());
			}

			//Creates a list to store all objects from source that doesn't implement
			//the current association
			ArrayList<TObject> objectsFromSourceNotInAssociation = new ArrayList<TObject>();
			
			//Adds all objects from source that were not marked as being in the association
			//to the objectsFromSourceNotInRelation list.
			for (TObject tObject : allObjectsFromSource) {
				if (!objectsIdsInAssociation.contains(tObject.getId())) {
					objectsFromSourceNotInAssociation.add(tObject);
				}
			}
			
			//Stores all objects from the association target in a list
			ArrayList<TObject> allObjectsFromTarget = objs.get(currentAssociation.getEType().getName());
			
			//Runs through the list of source objects that are not a source for this association
			//and add and axiom explicitly stating that such relationship doesn't exist
			//between it and any object of the target type
			//this axiom is needed due to the open world assumption existing in DL
			for (TObject currentSourceObject : objectsFromSourceNotInAssociation) {
				for (TObject currentTargetObject : allObjectsFromTarget) {
					
					//Creates and axiom describing the source object
					OWLClass owlObjectSource = owlDataFactory_.getOWLClass(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentSourceObject.getId() + OBJECT_POSFIX));
					
					//Creates and axiom describing the target object
					OWLClass owlObjectTarget = owlDataFactory_.getOWLClass(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentTargetObject.getId() + OBJECT_POSFIX));
					
					//Creates an axiom describing one association between the two objects 
					OWLObjectProperty owlEr = owlDataFactory_.getOWLObjectProperty(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentAssociation.getEOpposite().getEReferenceType().getName()
									+ currentAssociation.getName() + currentAssociation.getEReferenceType().getName() + ROLE_POSFIX));
					
					//Creates an axiom describing that the association between the two objects doesn't  exists
					OWLObjectSomeValuesFrom exists = owlDataFactory_.getOWLObjectSomeValuesFrom(owlEr, owlObjectTarget);
					OWLObjectComplementOf complement = owlDataFactory_.getOWLObjectComplementOf(exists);
					
					//Creates an axiom stating that the current source object is a subset of 
					//the previous axiom.
					OWLAxiom subsumAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlObjectSource, complement);
					//Adds the axiom to the resulting axiom list
					axiomList_.add(subsumAxiom);
				}
			}
			
			//Get the mapping between objects and the list of links of this association
			HashMap<TObject, ArrayList<TLink>> assoc = links.get(currentAssociation.getEOpposite().getEType().getName() + currentAssociation.getName());
			
			//runs through the list of source objects 
			for (TObject currentSourceObject : objectsInAssociationSource) {
				
				//Creates an list to store the objects related to the current object
				// through a link implementing the current association
				ArrayList<TObject> objectsRelated = new ArrayList<>();
				
				//run through the links that implement the current association and
				//have as source the current object
				for (TLink link : assoc.get(currentSourceObject)) {
					
					//Populates the list of related objects with the target objects
					//for the current object
					objectsRelated.add(objs.get(link.getType()).get(link.getPosition()));
					
					//Creates an OWLClass representing the current source object
					OWLClass owlObject = owlDataFactory_.getOWLClass(
							IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentSourceObject.getId() + OBJECT_POSFIX));
					
					//Creates and OWL Object Property represeting the object class association
					OWLObjectProperty owlEr = owlDataFactory_.getOWLObjectProperty(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentAssociation.getEOpposite().getEReferenceType().getName()
									+ currentAssociation.getName() + currentAssociation.getEReferenceType().getName() + ROLE_POSFIX));
					
					//Creates an OWLClass represeting the current target object
					OWLClass owlObjectTarget = owlDataFactory_
							.getOWLClass(IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX
									+ objs.get(link.getType()).get(link.getPosition()).getId() + OBJECT_POSFIX));
					
					//Creates an axiom stating that the current link has a Cardinality of exactly 1.
					OWLObjectExactCardinality cardExaclty = owlDataFactory_.getOWLObjectExactCardinality(1, owlEr,
							owlObjectTarget);
					
					//Creates an axiom stating that the current object is a subset of the axiom
					//that restricts the cardinality
					OWLAxiom subsumUnionAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlObject, cardExaclty);
					
					//Adds the axiom to axiom list
					axiomList_.add(subsumUnionAxiom);
				}
				
				//Creates an list to store all the objects from the target's type that doesn't relate
				//to the current source object. Such list is instantiated with all objects from target
				ArrayList<TObject> unrelatedObjects = new ArrayList<TObject>(allObjectsFromTarget);
				
				//remove from the unrelatedObjects list the objects that are related 
				//to the current source object
				unrelatedObjects.removeAll(objectsRelated);
				
				//runs through the unrelated objects list
				for (TObject tObjectTarget : unrelatedObjects) {
					
					//Creates an OWLCLass representing the current object
					OWLClass owlObjectSource = owlDataFactory_.getOWLClass(
							IRI.create(ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentSourceObject.getId() + OBJECT_POSFIX));
					
					//Creates an OWLClass representing the current unrelated target object
					OWLClass owlObjectTarget = owlDataFactory_.getOWLClass(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + tObjectTarget.getId() + OBJECT_POSFIX));
					
					//Creates an axiom representing the current association
					OWLObjectProperty owlEr = owlDataFactory_.getOWLObjectProperty(IRI.create(
							ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + currentAssociation.getEOpposite().getEReferenceType().getName()
									+ currentAssociation.getName() + currentAssociation.getEReferenceType().getName() + ROLE_POSFIX));
					
					//Creates an axiom stating that such association between the two objects
					//doesn't exits
					OWLObjectSomeValuesFrom exists = owlDataFactory_.getOWLObjectSomeValuesFrom(owlEr, owlObjectTarget);
					OWLObjectComplementOf complement = owlDataFactory_.getOWLObjectComplementOf(exists);
					
					//Creates an axiom stating that the current object is a subset
					//of the  previous axiom
					OWLAxiom subsumAxiom = owlDataFactory_.getOWLSubClassOfAxiom(owlObjectSource, complement);

					//Adds the axiom to axiom list
					axiomList_.add(subsumAxiom);
				}
			}
		}
	}

}
