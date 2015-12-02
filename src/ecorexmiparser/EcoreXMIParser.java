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

package ecorexmiparser;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EReference;
import org.xml.sax.Attributes;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;
import org.xml.sax.helpers.DefaultHandler;
import org.xml.sax.helpers.XMLReaderFactory;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.0.0
 * @since 1.0.0
 * 
 */
public class EcoreXMIParser {

	private String CONTAINERNAME = "XMIContainer";
	private final String OBJECT_PREFIX = "Object";
	private Map<String, ArrayList<TObject>> objectPool;
	private Map<String, ArrayList<TObject>> objectPoolSimplified;
	private Map<String, ArrayList<String>> inheritanceClosureMap;
	private Map<String, HashMap<TObject, ArrayList<TLink>>> linkPool;

	public EcoreXMIParser(ArrayList<EClass> classes, ArrayList<EReference> associations, String ePackageName) {
		CONTAINERNAME = String.format(CONTAINERNAME, ePackageName);
		objectPool = new HashMap<String, ArrayList<TObject>>();
		objectPoolSimplified = new HashMap<String, ArrayList<TObject>>();
		inheritanceClosureMap = new HashMap<String, ArrayList<String>>();
		for (EClass eClass : classes) {
			objectPool.put(eClass.getName(), new ArrayList<TObject>());
			objectPoolSimplified.put(eClass.getName(), new ArrayList<TObject>());
			ArrayList<EClass> toAns = new ArrayList<EClass>();
			toAns.add(eClass);
			inheritanceClosureMap.put(eClass.getName(), calculateInheritanceClosure(toAns));
		}
		linkPool = new HashMap<String, HashMap<TObject, ArrayList<TLink>>>();
		for (EReference eReference : associations) {
			linkPool.put(eReference.getEOpposite().getEType().getName() + eReference.getName(),
					new HashMap<TObject, ArrayList<TLink>>());
		}
	}

	private ArrayList<String> calculateInheritanceClosure(ArrayList<EClass> composedAnswer) {
		ArrayList<EClass> newClasses = new ArrayList<EClass>();
		boolean end = true;
		for (EClass eClass : composedAnswer) {
			if (!composedAnswer.containsAll(eClass.getESuperTypes())) {
				newClasses.addAll(eClass.getESuperTypes());
				end = false;
			}
		}
		if (end) {
			ArrayList<String> ans = new ArrayList<String>();
			for (EClass eClass : composedAnswer) {
				ans.add(eClass.getName());
			}
			return ans;
		} else {
			composedAnswer.addAll(newClasses);
			return calculateInheritanceClosure(composedAnswer);
		}
	}

	/**
	 * Parses the file. After this call a query method can be called.
	 */
	public void parse(String xmiSourceModel) {
		File objectModelFile = new File(xmiSourceModel);
		InputStream inputStream = null;
		try {
			{
				XMLReader xmlReader = XMLReaderFactory.createXMLReader();
				xmlReader.setContentHandler(new XMIHandler());
				inputStream = new FileInputStream(objectModelFile);
				xmlReader.parse(new InputSource(inputStream));
			}
		} catch (SAXException ex) {
			ex.printStackTrace();
		} catch (FileNotFoundException ex) {
			ex.printStackTrace();
		} catch (IOException ex) {
			ex.printStackTrace();
		} finally {
			try {
				inputStream.close();
			} catch (IOException ex) {
				ex.printStackTrace();
			}
		}
	}

	public Map<String, ArrayList<TObject>> getObjectPool() {
		return objectPool;
	}

	public Map<String, ArrayList<TObject>> getObjectPoolSimplified() {
		return objectPoolSimplified;
	}

	public Map<String, HashMap<TObject, ArrayList<TLink>>> getlinkPool() {
		return linkPool;
	}

	private class XMIHandler extends DefaultHandler {

		private int objectCounter;

		public XMIHandler() {
			objectCounter = 0;
		}

		@Override
		public void startElement(String uri, String localName, String qName, Attributes attributes)
				throws SAXException {
			if (!localName.equals(CONTAINERNAME)) {
				TObject obj = new TObject(OBJECT_PREFIX + objectCounter);
				objectCounter++;
				String type = localName.replaceFirst(OBJECT_PREFIX, "");
				int i = 0;
				if (attributes.getLocalName(0) != null && attributes.getLocalName(0).equals("type")) {
					type = attributes.getValue(0).split(":")[1];
					i++;
				}
				objectPoolSimplified.get(type).add(obj);
				for (String eClsName : inheritanceClosureMap.get(type)) {
					objectPool.get(eClsName).add(obj);
				}
				while (i < attributes.getLength()) {
					String keyName = "";
					for (String originAttribute : inheritanceClosureMap.get(type)) {
						keyName = originAttribute + attributes.getLocalName(i);
						if (linkPool.keySet().contains(keyName)) {
							break;
						}
					}
					HashMap<TObject, ArrayList<TLink>> map = linkPool.get(keyName);
					if (map != null) {
						if (map.get(obj) == null) {
							map.put(obj, new ArrayList<TLink>());
						}
						String value = attributes.getValue(i).replaceAll("//@", "");
						String[] values = value.split(" ");
						for (String val : values) {
							int typeIndex = 0;
							String typeName = val;
							typeIndex = Integer.valueOf(val.substring(val.lastIndexOf(".") + 1));
							typeName = val.substring(0, val.lastIndexOf("."));
							map.get(obj).add(new TLink(typeName, typeIndex));
						}
					}
					i++;
				}
			}
		}
	}
}
