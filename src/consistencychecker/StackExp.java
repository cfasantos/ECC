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

import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.ocl.expressions.IteratorExp;
import org.eclipse.ocl.expressions.OCLExpression;
import org.eclipse.ocl.expressions.OperationCallExp;
import org.eclipse.ocl.expressions.PropertyCallExp;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectProperty;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.0.0
 * @since 1.0.0
 * 
 */
public class StackExp {

	protected static final String SPACE = " ";
	protected static final String DOT = ".";
	protected static final String OCL_AS_TYPE = "oclAsType";
	protected static final String IS_EMPTY = "isEmpty";
	protected static final String SELECT = "select";
	protected static final String DOUBLE_COLON = "::";
	protected static final String BLANK = "";
	protected static final String ARROW = "->";
	protected static final String NOT_EMPTY = "notEmpty";
	protected static final String IMPLIES = "implies";
	protected static final String OR = "or";
	protected static final String AND = "and";
	protected static final String NOT = "not";
	protected static final String OCL_IS_TYPE_OF = "oclIsTypeOf";
	protected static final String PARENTHESIS = "()";
	protected static final String PARENTHESIS_FOR_FORMAT = "(%s)";
	protected static final String POUND_SIGN = "#";
	protected static final String CLASS_POSFIX = "class";
	protected static final String ROLE_POSFIX = "role";
	protected String PACKAGE_PREFIX;
	protected IRI ontologyIRI_;
	protected OWLDataFactory owlDataFactory_;
	protected OWLClassExpression topExp;
	protected boolean pushToSon;
	protected int stackPoint;
	protected StackElement[] stack;
	public StackExp fatherStack;
	protected String CLASS_NAME_BUILDER = "";

	public StackExp(StackExp fatherStack, IRI ontoIRI, String pkg) {
		pushToSon = false;
		stackPoint = 0;
		this.fatherStack = fatherStack;
		owlDataFactory_ = OWLManager.createOWLOntologyManager().getOWLDataFactory();
		ontologyIRI_ = ontoIRI;
		PACKAGE_PREFIX = pkg;
		topExp = null;
		CLASS_NAME_BUILDER = ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + "(" + "%s" + "[" + CLASS_POSFIX + "]" + ")";
	}

	public StackExp push(OCLExpression<EClassifier> c, boolean toSon) {
		StackExp result = this;
		if (stack == null) {
			stack = new StackElement[100];
		}
		stack[stackPoint] = new StackElement(this, ontologyIRI_, PACKAGE_PREFIX);
		stack[stackPoint].setExp(c);
		if (toSon) {
			result = stack[stackPoint].sourceStack;
		}
		stackPoint++;
		return result;
	}

	public StackExp pushToSon(OCLExpression<EClassifier> c, boolean toSon) {
		return stack[stackPoint - 1].sourceStack.push(c, toSon);
	}

	public void changeUpElementToSelect() {
		stack[stackPoint - 1].getExp().setName(SELECT);
	}

	public void endStack() {
		if (pushToSon) {
			stack[stackPoint - 1].endStack();
		} else {
			fatherStack.pushToSon = false;
		}
	}

	public StackElement pop() {
		stackPoint--;
		return stack[stackPoint];
	}

	public OCLExpression<EClassifier> getTopElementExpression() {
		int i = stackPoint - 1;
		return stack[i].getExp();
	}

	public OWLClassExpression resolveStack() {
		OWLClassExpression result = null;
		StackElement s = pop();
		OCLExpression<EClassifier> exp = s.getExpression();
		if (exp instanceof OperationCallExp) {
			OperationCallExp<EClassifier, EOperation> resExp = (OperationCallExp<EClassifier, EOperation>) exp;
			if (resExp.getReferredOperation().getName().equals(OCL_IS_TYPE_OF)) {
				String argumentName = resExp.getArgument().get(0).toString()
						.split(DOUBLE_COLON)[resExp.getArgument().get(0).toString().split(DOUBLE_COLON).length - 1];
				result = owlDataFactory_.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, argumentName)));
				// .create(ontologyIRI_
				// + POUND_SIGN + PACKAGE_PREFIX + argumentName +
				// CLASS_POSFIX));
			} else {
				if (resExp.getReferredOperation().getName().equals(NOT)) {
					result = owlDataFactory_.getOWLObjectComplementOf(this.resolveStack());
				} else {
					if (resExp.getReferredOperation().getName().equals(AND)) {
						OWLClassExpression rightSide = s.sourceStack.resolveStack();
						result = owlDataFactory_.getOWLObjectIntersectionOf(this.resolveStack(), rightSide);
					} else {
						if (resExp.getReferredOperation().getName().equals(OR)) {
							OWLClassExpression rightSide = s.sourceStack.resolveStack();
							result = owlDataFactory_.getOWLObjectUnionOf(this.resolveStack(), rightSide);
						} else {
							if (resExp.getReferredOperation().getName().equals(IMPLIES)) {
								OWLClassExpression rightSide = s.sourceStack.resolveStack();
								OWLClassExpression sourceComplement = owlDataFactory_
										.getOWLObjectComplementOf(this.resolveStack());
								result = owlDataFactory_.getOWLObjectUnionOf(sourceComplement, rightSide);
							} else {
								if (resExp.getReferredOperation().getName().equals(NOT_EMPTY)) {
									result = this.resolveStack();
								} else {
									if (resExp.getReferredOperation().getName().equals(IS_EMPTY)) {
										result = owlDataFactory_.getOWLObjectComplementOf(this.resolveStack());
									} else {
										if (resExp.getReferredOperation().getName().equals(OCL_AS_TYPE)) {
											String argumentName = resExp.getArgument().get(0).toString()
													.split(DOUBLE_COLON)[resExp.getArgument().get(0).toString()
															.split(DOUBLE_COLON).length - 1];
											OWLClass arg = owlDataFactory_.getOWLClass(
													IRI.create(String.format(CLASS_NAME_BUILDER, argumentName)));
											// .create(ontologyIRI_
											// + POUND_SIGN + PACKAGE_PREFIX +
											// argumentName + CLASS_POSFIX));
											topExp = owlDataFactory_.getOWLObjectIntersectionOf(arg, topExp);
											result = this.resolveStack();
										}
									}
								}
							}
						}
					}
				}
			}
		} else {
			if (exp instanceof PropertyCallExp) {
				PropertyCallExp<EClassifier, EReference> resExp = (PropertyCallExp<EClassifier, EReference>) exp;
				OWLObjectProperty roleLeft = owlDataFactory_.getOWLObjectProperty(IRI.create(ontologyIRI_ + POUND_SIGN
						+ PACKAGE_PREFIX + resExp.getReferredProperty().getEOpposite().getEType().getName()
						+ resExp.getReferredProperty().getName() + resExp.getReferredProperty().getEType().getName()
						+ ROLE_POSFIX));
				if (topExp == null) {
					topExp = owlDataFactory_.getOWLObjectSomeValuesFrom(roleLeft, owlDataFactory_.getOWLThing());
				} else {
					topExp = owlDataFactory_.getOWLObjectSomeValuesFrom(roleLeft, topExp);
				}
				if (stackPoint == 0) {
					result = topExp;
				} else {
					result = this.resolveStack();
				}
			} else {
				if (exp instanceof IteratorExp) {
					topExp = s.sourceStack.resolveStack();
					result = this.resolveStack();
				}
			}
		}
		return result;
	}

	public String print() {
		int sta = stackPoint;
		String ans = BLANK;
		StackElement s = pop();
		OCLExpression<EClassifier> elem = s.getExpression();
		if (elem instanceof OperationCallExp<?, ?>) {
			OperationCallExp<EClassifier, EOperation> resExp = (OperationCallExp<EClassifier, EOperation>) elem;
			if (resExp.getReferredOperation().getName().equals(OCL_IS_TYPE_OF)) {
				String argumentName = resExp.getArgument().get(0).toString()
						.split(DOUBLE_COLON)[resExp.getArgument().get(0).toString().split(DOUBLE_COLON).length - 1];
				ans = OCL_IS_TYPE_OF + String.format(PARENTHESIS_FOR_FORMAT, argumentName);
			} else {
				if (resExp.getReferredOperation().getName().equals(NOT)) {
					ans = NOT + String.format(PARENTHESIS_FOR_FORMAT, print());
				} else {
					if (resExp.getReferredOperation().getName().equals(AND)) {
						ans = print() + SPACE + AND + SPACE + s.sourceStack.print();
					} else {
						if (resExp.getReferredOperation().getName().equals(OR)) {
							ans = print() + SPACE + OR + SPACE + s.sourceStack.print();
						} else {
							if (resExp.getReferredOperation().getName().equals(IMPLIES)) {
								ans = print() + SPACE + IMPLIES + SPACE + s.sourceStack.print();
							} else {
								if (resExp.getReferredOperation().getName().equals(NOT_EMPTY)) {
									ans = print() + ARROW + NOT_EMPTY + PARENTHESIS;
								} else {
									if (resExp.getReferredOperation().getName().equals(IS_EMPTY)) {
										ans = print() + ARROW + IS_EMPTY + PARENTHESIS;
									} else {
										if (resExp.getReferredOperation().getName().equals(OCL_AS_TYPE)) {
											String argumentName = resExp.getArgument().get(0).toString()
													.split(DOUBLE_COLON)[resExp.getArgument().get(0).toString()
															.split(DOUBLE_COLON).length - 1];
											ans = OCL_IS_TYPE_OF + String.format(PARENTHESIS_FOR_FORMAT, argumentName);
										}
									}
								}
							}
						}
					}
				}
			}
		} else {
			if (elem instanceof PropertyCallExp) {
				PropertyCallExp<EClassifier, EReference> resExp = (PropertyCallExp<EClassifier, EReference>) elem;
				String role = resExp.getReferredProperty().getName();
				if (stackPoint == 0) {
					ans = role;
				} else {
					ans = DOT + role;
				}
			} else {
				if (elem instanceof IteratorExp) {
					if (stackPoint != 0) {
						ans = ARROW;
					}
					ans = print() + ans + elem.getName() + String.format(PARENTHESIS_FOR_FORMAT, s.sourceStack.print());
				}
			}
		}
		stackPoint = sta;
		return ans;
	}
}
