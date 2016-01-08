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

	public ECCAbstractVisitor(String context, IRI ontoIRI, String pkg) {
		super();
		mainSt = new StackExp(null, ontoIRI, pkg);
		currentSt = mainSt;
		owlDataFactory_ = OWLManager.createOWLOntologyManager().getOWLDataFactory();
		ontologyIRI_ = ontoIRI;
	}

	public void stack(OCLExpression<EClassifier> c, boolean b) {
		currentSt = currentSt.push(c, b);
	}

	public void stackIntoSonWithNoUpdate(OCLExpression<EClassifier> c, boolean b) {
		currentSt.pushToSon(c, b);
	}

	public void stackIntoSonWithUpdate(OCLExpression<EClassifier> c, boolean b) {
		currentSt = currentSt.pushToSon(c, b);
	}

	public void endStack() {
		currentSt = currentSt.fatherStack;
	}

	public void changeUpElementToSelect() {
		currentSt.changeUpElementToSelect();
	}

	public void endStackUntilSelect() {
		while (!(currentSt.getTopElementExpression() instanceof IteratorExp)) {
			currentSt = currentSt.fatherStack;
		}
	}

	@Override
	public OWLClassExpression handlePropertyCallExp(PropertyCallExp<EClassifier, EReference> callExp,
			OWLClassExpression sourceResult, List<OWLClassExpression> qualifierResults) {
		stack(callExp, false);
		if (callExp.eContainer() != null && callExp.eContainer().eContainer() != null
				&& callExp.eContainer().eContainer().eContainer() instanceof IteratorExp) {
			IteratorExp<EClassifier, EParameter> fatherExp = (IteratorExp<EClassifier, EParameter>) callExp.eContainer()
					.eContainer().eContainer();
			if (fatherExp.getSource() instanceof CollectionLiteralExp) {
				if (((CollectionItem) ((CollectionLiteralExp) fatherExp.getSource()).getPart().get(0))
						.getItem() == callExp) {
					stack(fatherExp, true);
				}
			}
			if (fatherExp.getBody() == callExp) {
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

	@Override
	public OWLClassExpression handleIteratorExp(IteratorExp<EClassifier, EParameter> callExp,
			OWLClassExpression sourceResult, List<OWLClassExpression> argumentResults, OWLClassExpression bodyResult) {
		if (callExp.getName().equals("exists")) {
			changeUpElementToSelect();
			EOperation notEmpty = EcoreFactoryImpl.eINSTANCE.createEOperation();
			notEmpty.setName("notEmpty");
			OperationCallExp<EClassifier, EOperation> OpCallExp = ExpressionsFactory.eINSTANCE.createOperationCallExp();
			OpCallExp.setReferredOperation(notEmpty);
			stack(OpCallExp, false);
		} else {
			if (callExp.getName().equals("forAll")) {
				changeUpElementToSelect();
				// Inserts a not into Son
				EOperation not = EcoreFactoryImpl.eINSTANCE.createEOperation();
				not.setName("not");
				OperationCallExp<EClassifier, EOperation> OpCallExpNot = ExpressionsFactory.eINSTANCE
						.createOperationCallExp();
				OpCallExpNot.setReferredOperation(not);
				stackIntoSonWithNoUpdate(OpCallExpNot, false);
				// inserts a isEmpty na pilha corrente
				EOperation isEmpty = EcoreFactoryImpl.eINSTANCE.createEOperation();
				isEmpty.setName("isEmpty");
				OperationCallExp<EClassifier, EOperation> OpCallExpNotEmpty = ExpressionsFactory.eINSTANCE
						.createOperationCallExp();
				OpCallExpNotEmpty.setReferredOperation(isEmpty);
				stack(OpCallExpNotEmpty, false);
			} else {
				if (callExp.getName().equals("select")) {
					if (callExp.eContainer() instanceof IteratorExp) {
						EOperation and = EcoreFactoryImpl.eINSTANCE.createEOperation();
						and.setName("and");
						OperationCallExp<EClassifier, EOperation> OpCallExpAnd = ExpressionsFactory.eINSTANCE
								.createOperationCallExp();
						OpCallExpAnd.setReferredOperation(and);
						stackIntoSonWithUpdate(OpCallExpAnd, true);
					} else {
						if (callExp.getSource() instanceof IteratorExp) {
							endStackUntilSelect();
						}
					}
				}
			}
		}

		return result;
	}

	@Override
	public OWLClassExpression handleOperationCallExp(OperationCallExp<EClassifier, EOperation> callExp,
			OWLClassExpression sourceResult, List<OWLClassExpression> argumentResults) {
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
			if (callExp.getReferredOperation().getName().equals("oclIsTypeOf")
					|| callExp.getReferredOperation().getName().equals("oclAsType")) {
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
							if (callExp.getReferredOperation().getName().equals("not")) {
								if (callExp.getSource() instanceof OperationCallExp) {
									OperationCallExp<EClassifier, EOperation> son = (OperationCallExp<EClassifier, EOperation>) callExp
											.getSource();
									if (!son.getReferredOperation().getName().equals("notEmpty")
											&& !son.getReferredOperation().getName().equals("isEmpty")) {
										stack(callExp, false);
									}
								}
							}
						}
					}
				}
			}
		}
		if (callExp.eContainer() instanceof OperationCallExp) {
			OperationCallExp<EClassifier, EOperation> fatherExp = (OperationCallExp<EClassifier, EOperation>) callExp
					.eContainer();
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
		return result;
	}
}
