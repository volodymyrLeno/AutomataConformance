/*
 *  Copyright (C) 2018 Raffaele Conforti (www.raffaeleconforti.com)
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.raffaeleconforti.java.raffaeleconforti.memorylog;

import com.google.common.collect.Interner;
import com.google.common.collect.Interners;
import org.deckfour.xes.extension.XExtension;
import org.deckfour.xes.factory.XFactory;
import org.deckfour.xes.id.XID;
import org.deckfour.xes.model.*;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.ObjectIntHashMap;

import java.net.URI;
import java.util.Date;

/**
 * Created by Raffaele Conforti (conforti.raffaele@gmail.com) on 4/08/2016.
 */
public class XFactoryMemoryImpl implements XFactory {

    private int[] counter = new int[1];
    private IntObjectHashMap<XEvent> intToEvent = new IntObjectHashMap<>();
    private ObjectIntHashMap<XEvent> eventToInt = new ObjectIntHashMap<>();

    // Use String interning to save memory
    private Interner<String> interner;

    public XFactoryMemoryImpl() {
        super();
        // Use an weak references as this factory may stay around in the XFactoryRegistry for a long time
        interner = Interners.newWeakInterner();
    }

    private String intern(String s) {
        return interner.intern(s);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#getAuthor()
     */
    public String getAuthor() {
        return "Christian W. Günther";
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#getDescription()
     */
    public String getDescription() {
        return "Creates naive implementations for all available "
                + "model hierarchy elements, i.e., no optimizations "
                + "will be employed.";
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#getName()
     */
    public String getName() {
        return "Standard / naive";
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#getUri()
     */
    public URI getUri() {
        return URI.create("http://www.xes-standard.org/");
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#getVendor()
     */
    public String getVendor() {
        return "xes-standard.org";
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createLog()
     */
    public XLog createLog() {
//        return new XLogImpl(new XAttributeMapLazyImpl<XAttributeMapImpl>(XAttributeMapImpl.class));
        return new XLogImpl(null, counter, intToEvent, eventToInt);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.factory.XFactory#createLog(org.deckfour.xes.model.XAttributeMap)
     */
    public XLog createLog(XAttributeMap attributes) {
        return new XLogImpl(attributes, counter, intToEvent, eventToInt);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createTrace()
     */
    public XTrace createTrace() {
//        return new XTraceImpl(new XAttributeMapLazyImpl<XAttributeMapImpl>(XAttributeMapImpl.class));
        return new XTraceImpl(null, counter, intToEvent, eventToInt);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.factory.XFactory#createTrace(org.deckfour.xes.model.XAttributeMap)
     */
    public XTrace createTrace(XAttributeMap attributes) {
        return new XTraceImpl(attributes, counter, intToEvent, eventToInt);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createEvent()
     */
    public XEvent createEvent() {
        return new XEventImpl();
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.factory.XFactory#createEvent(org.deckfour.xes.model.XAttributeMap)
     */
    public XEvent createEvent(XAttributeMap attributes) {
        return new XEventImpl(attributes);
    }

    /*
     * (non-Javadoc)
     * @see org.deckfour.xes.factory.XFactory#createEvent(org.deckfour.xes.id.XID, org.deckfour.xes.model.XAttributeMap)
     */
    public XEvent createEvent(XID id, XAttributeMap attributes) {
        return new XEventImpl(id, attributes);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeMap()
     */
    public XAttributeMap createAttributeMap() {
        return new XAttributeMapImpl();
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeBoolean(java.lang.String, boolean, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeBoolean createAttributeBoolean(String key, boolean value,
                                                    XExtension extension) {
        return new XAttributeBooleanImpl(intern(key), value, extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeContinuous(java.lang.String, double, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeContinuous createAttributeContinuous(String key,
                                                          double value, XExtension extension) {
        return new XAttributeContinuousImpl(intern(key), value, extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeDiscrete(java.lang.String, long, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeDiscrete createAttributeDiscrete(String key, long value,
                                                      XExtension extension) {
        return new XAttributeDiscreteImpl(intern(key), value, extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeLiteral(java.lang.String, java.lang.String, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeLiteral createAttributeLiteral(String key, String value,
                                                    XExtension extension) {
        return new XAttributeLiteralImpl(intern(key), intern(value), extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeTimestamp(java.lang.String, java.util.Date, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeTimestamp createAttributeTimestamp(String key, Date value,
                                                        XExtension extension) {
        return new XAttributeTimestampImpl(intern(key), value, extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeTimestamp(java.lang.String, long, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeTimestamp createAttributeTimestamp(String key,
                                                        long millis, XExtension extension) {
        return new XAttributeTimestampImpl(intern(key), millis, extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.model.factory.XModelFactory#createAttributeID(java.lang.String, org.deckfour.xes.id.XID, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeID createAttributeID(String key, XID value,
                                          XExtension extension) {
        return new XAttributeIDImpl(intern(key), value, extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.factory.XFactory#createAttributeList(java.lang.String, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeList createAttributeList(String key, XExtension extension) {
        return new XAttributeListImpl(intern(key), extension);
    }

    /* (non-Javadoc)
     * @see org.deckfour.xes.factory.XFactory#createAttributeContainer(java.lang.String, org.deckfour.xes.extension.XExtension)
     */
    public XAttributeContainer createAttributeContainer(String key, XExtension extension) {
        return new XAttributeContainerImpl(intern(key), extension);
    }
}
