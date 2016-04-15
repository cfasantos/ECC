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

import java.util.List;

import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EParameter;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.impl.EcoreFactoryImpl;
import org.eclipse.ocl.ecore.Constraint;
import org.eclipse.ocl.expressions.CollectionItem;
import org.eclipse.ocl.expressions.CollectionLiteralExp;
import org.eclipse.ocl.expressions.ExpressionsFactory;
import org.eclipse.ocl.expressions.IteratorExp;
import org.eclipse.ocl.expressions.OCLExpression;
import org.eclipse.ocl.expressions.OperationCallExp;
import org.eclipse.ocl.expressions.PropertyCallExp;
import org.eclipse.ocl.utilities.AbstractVisitor;
import org.eclipse.uml2.uml.CallOperationAction;
import org.eclipse.uml2.uml.EnumerationLiteral;
import org.eclipse.uml2.uml.SendSignalAction;
import org.eclipse.uml2.uml.State;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.1.0
 * @since 1.0.0
 * 
 * @see <a href="http://dx.doi.org/10.1016/j.datak.2011.09.004" target=
 *      _blank>http://dx.doi.org/10.1016/j.datak.2011.09.004</a>
 */
public class ECCAbstractVisitor extends
		AbstractVisitor<OWLClassExpression, EClassifier, EOperation, EReference, EnumerationLiteral, EParameter, State, CallOperationAction, SendSignalAction, Constraint> {

	public OWLDataFactory owlDataFactory_;
	public StackExp mainSt;
	public StackExp currentSt;
	public IRI ontologyIRI_;

	public ECCAbstractVisitor(IRI ontoIRI, String pkg) {
		super();
		mainSt = new StackExp(null, ontoIRI, pkg);
		currentSt = mainSt;
		owlDataFactory_ = OWLManager.createOWLOntologyManager().getOWLDataFactory();
		ontologyIRI_ = ontoIRI;
	}

	/**
	 * Stores the OCL Expression in a multi-level stack
	 * 
	 * @param expression
	 * 		The expression that will be added to the stack representing the whole expression
	 * @param toInnerStack
	 * 		If "true", then the current stack will be changed to a inner level in the stack
	 */
	public void stack(OCLExpression<EClassifier> expression, boolean toInnerStack) {
		currentSt = currentSt.push(expression, toInnerStack);
	}

	/**
	 * Stores the OCL Expression in the inner stack of the multi-level stack
	 * 
	 * @param expression
	 * 		The expression that will be added to the stack
	 * @param update
	 * 		If "true", then the current stack will be changed to a inner level in the stack
	 */
	public void stackIntoSon(OCLExpression<EClassifier> expression, boolean update) {
		if(update){
			currentSt = currentSt.pushToSon(expression, update);
		}else{
			currentSt.pushToSon(expression, update);
		}
	}

	/**
	 * Sets the current stack as the upper level in the multi-level stack
	 */
	public void endStack() {
		currentSt = currentSt.fatherStack;
	}

	/**
	 * Normalization method used when normalizing OCL iterators. Change the iterator Expression to a select.
	 */
	private void changeUpElementToSelect() {
		//Changes the element at top of the stack (currently being normalized) to a select expression
		currentSt.changeUpElementToSelect();
	}

	/**
	 * Normalization method used to find the next "Select" iterator in the multi-level stack
	 */
	public void endStackUntilSelect() {
		while (!(currentSt.getTopElementExpression() instanceof IteratorExp)) {
			currentSt = currentSt.fatherStack;
		}
	}

	/**
	 * Normalize OCL Expressions that are Property calls
	 * 
	 * @see <a href="http://www.inf.unibz.it/~calvanese/papers-html/DL-2012-ocl.html" target=
	 *  _blank>OCL-Lite: A Decidable (Yet Expressive) Fragment of OCL/a>
	 * 
	 */
	@Override
	public OWLClassExpression handlePropertyCallExp(PropertyCallExp<EClassifier, EReference> callExp,
			OWLClassExpression sourceResult, List<OWLClassExpression> qualifierResults) {
		stack(callExp, false);
		//Checks if the property is being applied on an iterator
		if (callExp.eContainer() != null && callExp.eContainer().eContainer() != null
				&& callExp.eContainer().eContainer().eContainer() instanceof IteratorExp) {
			//Instantiates a variable representing the iterator
			IteratorExp<EClassifier, EParameter> fatherExp = (IteratorExp<EClassifier, EParameter>) callExp.eContainer()
					.eContainer().eContainer();
			//Checks if the iterator is being applied on other iterator
			if (fatherExp.getSource() instanceof CollectionLiteralExp) {
				//Checks if 
				if (((CollectionItem) ((CollectionLiteralExp) fatherExp.getSource()).getPart().get(0))
						.getItem() == callExp) {
					//Stacks the iterator in the inner stack of the current stackExp
					stack(fatherExp, true);
				}
			}
			//Checks the Iterator is being directly restricted by the property being normalized
			if (fatherExp.getBody() == callExp) {
				//Ends the stack representing the iterator
				endStack();
			}
		} else {
			if (callExp.eContainer() instanceof IteratorExp) {
				IteratorExp<EClassifier, EParameter> fatherExp = (IteratorExp<EClassifier, EParameter>) callExp
						.eContainer();
				if (fatherExp.getSource() instanceof PropertyCallExp) {
					if (((PropertyCallExp) fatherExp.getSource()) == callExp) {
						stack(fatherExp, true);
					}
				}
				if (fatherExp.getBody() == callExp) {
					endStack();
				}
			}
		}
		return result;
	}

	/**
	 * Normalize OCL Expressions that are Iterators
	 * 
	 * @see <a href="http://www.inf.unibz.it/~calvanese/papers-html/DL-2012-ocl.html" target=
	 *  _blank>OCL-Lite: A Decidable (Yet Expressive) Fragment of OCL</a>
	 * 
	 */
	@Override
	public OWLClassExpression handleIteratorExp(IteratorExp<EClassifier, EParameter> callExp,
			OWLClassExpression sourceResult, List<OWLClassExpression> argumentResults, OWLClassExpression bodyResult) {
		//Verifies the iterator being handled and executes the proper normalization process
		switch(callExp.getName()){
		//Apply the normalization described in "rule a)", "Table 1" from the paper 
		//"OCL-Lite: A Decidable (Yet Expressive) Fragment of OCL"  
		case "exists":
			//Change the top stacked element from an "exists" to "select"
			changeUpElementToSelect();
			//Creates an "notEmpty" Operator
			EOperation notEmpty = EcoreFactoryImpl.eINSTANCE.createEOperation();
			notEmpty.setName("notEmpty");
			OperationCallExp<EClassifier, EOperation> notEmptyExp = ExpressionsFactory.eINSTANCE.createOperationCallExp();
			notEmptyExp.setReferredOperation(notEmpty);
			//Adds the "notEmpty" Operator at the stack
			stack(notEmptyExp, false);
			break;
		//Apply the normalization described in "rule b)", "Table 1" from the paper 
		//"OCL-Lite: A Decidable (Yet Expressive) Fragment of OCL"  
		case "forall":
			//Change the top stacked element from an "forall" to "select"
			changeUpElementToSelect();
			//Creates an "not" Operator
			EOperation not = EcoreFactoryImpl.eINSTANCE.createEOperation();
			not.setName("not");
			OperationCallExp<EClassifier, EOperation> OpCallExpNot = ExpressionsFactory.eINSTANCE
					.createOperationCallExp();
			OpCallExpNot.setReferredOperation(not);
			//Adds the "not" Operator at the stack representing the condition in the "forall" operator
			stackIntoSon(OpCallExpNot, false);
			EOperation isEmpty = EcoreFactoryImpl.eINSTANCE.createEOperation();
			//Creates an "isEmpty" Operator
			isEmpty.setName("isEmpty");
			OperationCallExp<EClassifier, EOperation> OpCallExpNotEmpty = ExpressionsFactory.eINSTANCE
					.createOperationCallExp();
			OpCallExpNotEmpty.setReferredOperation(isEmpty);
			stack(OpCallExpNotEmpty, false);
			//Add the "isEmpty" operator at the top of the stack
			break;
		//Apply the normalization described in "rule c)", "Table 1" from the paper 
		//"OCL-Lite: A Decidable (Yet Expressive) Fragment of OCL"
		case "select":
			//Checks if the "select" iterator is applied in sequence with another "select" iterator
			if (callExp.eContainer() instanceof IteratorExp) {
				//creates an "and" operator
				EOperation and = EcoreFactoryImpl.eINSTANCE.createEOperation();
				and.setName("and");
				OperationCallExp<EClassifier, EOperation> OpCallExpAnd = ExpressionsFactory.eINSTANCE
						.createOperationCallExp();
				OpCallExpAnd.setReferredOperation(and);
				//Includes the "and" operator in the stack
				stackIntoSon(OpCallExpAnd, true);
			} else {
				//If the select operator isn't applied in sequence with another "select" iterator
				//But rather as a condition in a iterator, then changes the current stack
				//to the first "select" operator in the stack
				if (callExp.getSource() instanceof IteratorExp) {
					endStackUntilSelect();
				}
			}
			break;
		default:
			break;
		}
		//Returns a mockup variable, always null
		return result;
	}

	/**
	 * Normalize OCL Expressions that are Operations
	 * 
	 * @see <a href="http://www.inf.unibz.it/~calvanese/papers-html/DL-2012-ocl.html" target=
	 *  _blank>OCL-Lite: A Decidable (Yet Expressive) Fragment of OCL/a>
	 * 
	 */
	@Override
	public OWLClassExpression handleOperationCallExp(OperationCallExp<EClassifier, EOperation> callExp,
			OWLClassExpression sourceResult, List<OWLClassExpression> argumentResults) {
		//Checks if the operation being normalized is an conjunction, disjunction or implication
		if (callExp.getReferredOperation().getName().equals("and")
				|| callExp.getReferredOperation().getName().equals("or")
				|| callExp.getReferredOperation().getName().equals("implies")) {
			IteratorExp<EClassifier, EParameter> fatherExp = null;
			if (callExp.eContainer() != null && callExp.eContainer().eContainer() != null
					&& callExp.eContainer().eContainer().eContainer() instanceof IteratorExp) {
				fatherExp = (IteratorExp<EClassifier, EParameter>) callExp.eContainer().eContainer().eContainer();
			}
			if (fatherExp != null) {
				if (fatherExp.getBody() == callExp) {
					endStack();
				}
			}
		} else {
			//Check if the Operation being normalized is an ocl type verification or conversion
			if (callExp.getReferredOperation().getName().equals("oclIsTypeOf")
					|| callExp.getReferredOperation().getName().equals("oclAsType")) {
				//Stacks the OCL type operator
				stack(callExp, false);
			} else {
				if (callExp.getReferredOperation().getName().equals("size")) {
					if (((OperationCallExp<EClassifier, EOperation>) callExp.eContainer()).getReferredOperation()
							.getName().equals(">")) {
						callExp.getReferredOperation().setName("notEmpty");
					} else {
						callExp.getReferredOperation().setName("isEmpty");
					}
					stack(callExp, false);
				} else {
					if (callExp.getReferredOperation().getName().equals("isEmpty")) {
						if (callExp.eContainer() instanceof OperationCallExp) {
							if (((OperationCallExp<EClassifier, EOperation>) callExp.eContainer())
									.getReferredOperation().getName().equals("not")) {
								callExp.getReferredOperation().setName("notEmpty");
							}
						}
						stack(callExp, false);
					} else {
						if (callExp.getReferredOperation().getName().equals("notEmpty")) {
							if (callExp.eContainer() instanceof OperationCallExp) {
								if (((OperationCallExp<EClassifier, EOperation>) callExp.eContainer())
										.getReferredOperation().getName().equals("not")) {
									callExp.getReferredOperation().setName("isEmpty");
								}
							}
							stack(callExp, false);
						} else {
							//Checks if the operation beign normalized is an "not" operator
							if (callExp.getReferredOperation().getName().equals("not")) {
								//Checks if the expression to which the operator "not" is applied is also an operator expression.
								if (callExp.getSource() instanceof OperationCallExp) {
									//Stores the expression to which the operator "not" is applied in the "targetExpression" variable
									OperationCallExp<EClassifier, EOperation> targetExpression = (OperationCallExp<EClassifier, EOperation>) callExp
											.getSource();
									//Checks if the targeted expression of the "not" operator isn't a verification for Emptiness.
									if (!targetExpression.getReferredOperation().getName().equals("notEmpty")
											&& !targetExpression.getReferredOperation().getName().equals("isEmpty")) {
										//Stacks the "not" operator 
										stack(callExp, false);
									}
								}
							}
						}
					}
				}
			}
		}
		//Checks if the operation being normalized is contained in another operation
		if (callExp.eContainer() instanceof OperationCallExp) {
			OperationCallExp<EClassifier, EOperation> fatherExp = (OperationCallExp<EClassifier, EOperation>) callExp
					.eContainer();
			//Checks if the operation being normalized is an conjunction, disjunction or implication
			if (fatherExp.getReferredOperation().getName().equals("and")
					|| fatherExp.getReferredOperation().getName().equals("or")
					|| fatherExp.getReferredOperation().getName().equals("implies")) {
				if (fatherExp.getSource() == callExp) {
					stack(fatherExp, true);
				}
				if (fatherExp.getArgument().get(0) == callExp) {
					endStack();
				}

			}
		} else {
			if (callExp.eContainer() instanceof IteratorExp) {
				IteratorExp<EClassifier, EParameter> fatherExp = (IteratorExp<EClassifier, EParameter>) callExp
						.eContainer();
				if (fatherExp.getSource() == callExp) {
					stack(fatherExp, true);
				}
				if (fatherExp.getBody() == callExp) {
					endStack();
				}

			}
		}
		//Returns a mockup variable, always null
		return result;
	}
}
