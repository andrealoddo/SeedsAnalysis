
import java.awt.*;
import java.awt.geom.Point2D;
import java.awt.image.IndexColorModel;
import java.text.NumberFormat;
import java.util.Properties;
import ij.*;
import ij.gui.*;
import ij.process.*;
import ij.measure.*;
import ij.text.*;
import ij.plugin.*;
import ij.plugin.filter.*;
import ij.plugin.filter.Analyzer;
import ij.plugin.frame.Recorder;
import ij.plugin.frame.RoiManager;
import ij.plugin.frame.ThresholdAdjuster;
import ij.plugin.Colors;
import ij.measure.Measurements;
import ij.measure.ResultsTable;
import ij.macro.Interpreter;
import java.util.ArrayList;
import java.util.Arrays;
import ij.util.Tools;
import java.lang.Object;
import java.util.Vector;
import java.util.function.DoubleToLongFunction;
import ij.plugin.ChannelSplitter;


public class Seeds_Analysis_Plugin_ implements PlugInFilter, Measurements {

    //Display results in the ImageJ console.
    public static final int SHOW_RESULTS = 1;

    // Obsolete, replaced by  DISPLAY_SUMMARY
    public static final int SHOW_SUMMARY = 2;

    // Display image containing outlines of measured particles.
    public static final int SHOW_OUTLINES = 4;

    // Do not measure particles touching edge of image.
    public static final int EXCLUDE_EDGE_PARTICLES = 8;

    // Display image containing grayscales masks that identify measured particles.
    public static final int SHOW_ROI_MASKS = 16;

    // Display a progress bar.
    public static final int SHOW_PROGRESS = 32;

    // Clear "Results" window before starting.
    public static final int CLEAR_WORKSHEET = 64;

    // Record starting coordinates so outline can be recreated later using doWand(x,y).
    public static final int RECORD_STARTS = 128;

    // Display a summary.
    public static final int DISPLAY_SUMMARY = 256;

    // Do not display particle outline image.
    public static final int SHOW_NONE = 512;

    // Flood fill to ignore interior holes.
    public static final int INCLUDE_HOLES = 1024;

    // Add particles to ROI Manager.
    public static final int ADD_TO_MANAGER = 2048;

    // Display image containing binary masks of measured particles.
    public static final int SHOW_MASKS = 4096;

    // Use 4-connected particle tracing.
    public static final int FOUR_CONNECTED = 8192;

    // Replace original image with masks.
    public static final int IN_SITU_SHOW = 16384;

    // Display particle outlines as an overlay.
    public static final int SHOW_OVERLAY_OUTLINES = 32768;

    // Display filled particle as an overlay.
    public static final int SHOW_OVERLAY_MASKS = 65536;

    static final String OPTIONS = "ap.options";

    static final int BYTE=0, SHORT=1, FLOAT=2, RGB=3;
    static final double DEFAULT_MIN_SIZE = 0.0;
    static final double DEFAULT_MAX_SIZE = Double.POSITIVE_INFINITY;

    private static double staticMinSize = 0.0;
    private static double staticMaxSize = DEFAULT_MAX_SIZE;
    private static boolean pixelUnits;
    private static int staticOptions = Prefs.getInt(OPTIONS,CLEAR_WORKSHEET);
    private static String[] showStrings = {"Nothing", "Outlines", "Bare Outlines", "Ellipses", "Masks", "Count Masks", "Overlay", "Overlay Masks"};
    private static double staticMinCircularity=0.0, staticMaxCircularity=1.0;

    protected static final int NOTHING=0, OUTLINES=1, BARE_OUTLINES=2, ELLIPSES=3, MASKS=4, ROI_MASKS=5,
            OVERLAY_OUTLINES=6, OVERLAY_MASKS=7;
    protected static int staticShowChoice;
    protected ImagePlus imp;
    protected ResultsTable rt;
    protected Analyzer analyzer;
    protected int slice;
    protected boolean processStack;
    protected boolean showResults,excludeEdgeParticles,showSizeDistribution,
            resetCounter,showProgress, recordStarts, displaySummary, floodFill,
            addToManager, inSituShow;

    private boolean showResultsWindow = true;
    private double level1, level2;
    private double minSize, maxSize;
    private double minCircularity, maxCircularity;
    private int showChoice;
    private int options;
    private int measurements;
    private Calibration calibration;
    private String arg;
    private double fillColor;
    private boolean thresholdingLUT;
    private ImageProcessor drawIP;
    private int width,height;
    private boolean canceled;
    private ImageStack outlines;
    private IndexColorModel customLut;
    private int particleCount;
    private int maxParticleCount = 0;
    private int totalCount;
    private ResultsTable summaryTable;
    private Wand wand;
    private int imageType, imageType2;
    private boolean roiNeedsImage;
    private int minX, maxX, minY, maxY;
    private ImagePlus redirectImp;
    private ImageProcessor redirectIP;
    private PolygonFiller pf;
    private Roi saveRoi;
    private int beginningCount;
    private Rectangle r;
    private ImageProcessor mask;
    private double totalArea;
    private FloodFiller ff;
    private Polygon polygon;
    private RoiManager roiManager;
    private static RoiManager staticRoiManager;
    private static ResultsTable staticResultsTable;
    private ImagePlus outputImage;
    private boolean hideOutputImage;
    private int roiType;
    private int wandMode = Wand.LEGACY_MODE;
    private Overlay overlay;
    boolean blackBackground;
    private static int defaultFontSize = 9;
    private static int nextFontSize = defaultFontSize;
    private static Color defaultFontColor = Color.red;
    private static Color nextFontColor = defaultFontColor;
    private static int nextLineWidth = 1;
    private int fontSize = nextFontSize;
    private Color fontColor = nextFontColor;
    private int lineWidth = nextLineWidth;
    private boolean noThreshold;
    private boolean calledByPlugin;
    private boolean hyperstack;
    static int firstParticle, lastParticle; //aggiunto da me
    private GenericDialog gd_c; // attributo di classe che verrà linkato a gd per aver accesso all'oggetto genericDialog da qualsiasi punto della classe
    boolean  doArea, doPerimeter, doFeret, doCenterOfMass, doCentroid, doCircularity, doEllipse, doKurtosis, doMean,
            doMedian, doMinMax, doMode, doRectangularity, doSkewness, doStdDev;
    ImagePlus splitRGB [];
    ImagePlus HSI[];
    private double [][] glcm;

    /** Constructs a ParticleAnalyzer.
     @param options  a flag word created by Oring SHOW_RESULTS, EXCLUDE_EDGE_PARTICLES, etc.
     @param measurements a flag word created by ORing constants defined in the Measurements interface
     @param rt       a ResultsTable where the measurements will be stored
     @param minSize  the smallest particle size in pixels
     @param maxSize  the largest particle size in pixels
     @param minCirc  minimum circularity
     @param maxCirc  maximum circularity
     */
    public Seeds_Analysis_Plugin_(int options, int measurements, ResultsTable rt, double minSize, double maxSize, double minCirc, double maxCirc) {
        this.options = options;
        this.measurements = measurements;
        this.rt = rt;
        if (this.rt==null)
            this.rt = new ResultsTable();
        this.minSize = minSize;
        this.maxSize = maxSize;
        this.minCircularity = minCirc;
        this.maxCircularity = maxCirc;
        slice = 1;
        if ((options&SHOW_ROI_MASKS)!=0)
            showChoice = ROI_MASKS;
        if ((options&SHOW_OVERLAY_OUTLINES)!=0)
            showChoice = OVERLAY_OUTLINES;
        if ((options&SHOW_OVERLAY_MASKS)!=0)
            showChoice = OVERLAY_MASKS;
        if ((options&SHOW_OUTLINES)!=0)
            showChoice = OUTLINES;
        if ((options&SHOW_MASKS)!=0)
            showChoice = MASKS;
        if ((options&SHOW_NONE)!=0)
            showChoice = NOTHING;
        if ((options&FOUR_CONNECTED)!=0) {
            wandMode = Wand.FOUR_CONNECTED;
            options |= INCLUDE_HOLES;
        }
        nextFontSize = defaultFontSize;
        nextFontColor = defaultFontColor;
        nextLineWidth = 1;
        //calledByPlugin = true;
    }

    /** Constructs a ParticleAnalyzer using the default min and max circularity values (0 and 1). */
    public Seeds_Analysis_Plugin_(int options, int measurements, ResultsTable rt, double minSize, double maxSize) {
        this(options, measurements, rt, minSize, maxSize, 0.0, 1.0);
    }

    /** Default constructor */
    public Seeds_Analysis_Plugin_() {
        slice = 1;
    }

    public int setup(String arg, ImagePlus imp) {
        this.arg = arg;
        this.imp = imp;
        if (imp==null) {
            IJ.noImage();
            return DONE;//DONE 4096
        }
        if (imp.getBitDepth()==24 && !isThresholdedRGB(imp)) {
            IJ.error("Seeds",
                    "RGB images must be thresholded using\n"
                            +"Image>Adjust>Color Threshold.");
            return DONE;//DONE 4096
        }
        if (!showDialog())
            return DONE;//DONE 4096
        int baseFlags = DOES_ALL+NO_CHANGES+NO_UNDO;//NO_CHANGES
        int flags = IJ.setupDialog(imp, baseFlags); //funzione riportata giù
        processStack = (flags&DOES_STACKS)!=0;//DOES_STACKS 32
        slice = 0;
        saveRoi = imp.getRoi();
        if (saveRoi!=null && saveRoi.getType()!=Roi.RECTANGLE && saveRoi.isArea())
            polygon = saveRoi.getPolygon();
        imp.startTiming();
        nextFontSize = defaultFontSize;
        nextFontColor = defaultFontColor;
        nextLineWidth = 1;
        return flags;
    }

    public void run(ImageProcessor ip) {
        if (canceled)
            return;
        slice++;
        if (imp.getStackSize()>1 && processStack)
            imp.setSlice(slice);
        if (imp.getType()==ImagePlus.COLOR_RGB) {
            ip = (ImageProcessor)imp.getProperty("Mask");
            ip.setThreshold(255, 255, ImageProcessor.NO_LUT_UPDATE);
            ip.setRoi(imp.getRoi());
            ChannelSplitter chan = new ChannelSplitter();
            splitRGB = chan.split(imp);
            HSI = getHSIImagePluses(imp);

        }
        if (!analyze(imp, ip))
            canceled = true;
        if (slice==imp.getStackSize()) {
            imp.updateAndDraw();
            if (saveRoi!=null) imp.setRoi(saveRoi);
        }
        calcGLCM(ip);
    }

    /** Displays a modal options dialog. */
    public boolean showDialog() {
        Calibration cal = imp!=null?imp.getCalibration():(new Calibration());
        double unitSquared = cal.pixelWidth*cal.pixelHeight;
        boolean nextMeasure, flagb;//aggiunto da me
        int i, numbOfSpaces;
        if (pixelUnits)
            unitSquared = 1.0;
        if (Macro.getOptions()!=null) {
            boolean oldMacro = updateMacroOptions();
            if (oldMacro) unitSquared = 1.0;
            staticMinSize = 0.0;
            staticMaxSize = DEFAULT_MAX_SIZE;
            staticMinCircularity=0.0;
            staticMaxCircularity=1.0;
            staticShowChoice = NOTHING;
        }
        GenericDialog gd = new GenericDialog("Seeds Analysis");
        this.gd_c = gd; // gd_c viene linkato a gd
        minSize = staticMinSize;
        maxSize = staticMaxSize;
        minCircularity = staticMinCircularity;
        maxCircularity = staticMaxCircularity;
        showChoice = staticShowChoice;
        if (maxSize==999999)
            maxSize = DEFAULT_MAX_SIZE;
        options = staticOptions;
        String unit = cal.getUnit();
        boolean scaled = cal.scaled();
        String units = unit+"^2";
        int places = 0;
        double cmin = minSize*unitSquared;
        if ((int)cmin!=cmin)
            places = 2;
        double cmax = maxSize*unitSquared;
        if ((int)cmax!=cmax && cmax!=DEFAULT_MAX_SIZE)
            places = 2;
        String minStr = ResultsTable.d2s(cmin,places);
        if (minStr.indexOf("-")!=-1) {
            for (i = places; i<=6; i++) {
                minStr = ResultsTable.d2s(cmin, i);
                if (minStr.indexOf("-")==-1) break;
            }
        }
        String maxStr = ResultsTable.d2s(cmax, places);
        if (maxStr.indexOf("-")!=-1) {
            for (i = places; i<=6; i++) {
                maxStr = ResultsTable.d2s(cmax, i);
                if (maxStr.indexOf("-")==-1) break;
            }
        }
        if (scaled)
            gd.setInsets(5, 0, 0);
        //gd.addImage(imp); //aggiunto da me
        gd.addStringField("Size ("+units+"):", minStr+"-"+maxStr, 12);
        if (scaled) {
            gd.setInsets(0, 40, 5);
            gd.addCheckbox("Pixel units", pixelUnits);
        }
        Font g = new Font("g", Font.BOLD, 14);
        gd.addStringField("Circularity:", IJ.d2s(minCircularity)+"-"+IJ.d2s(maxCircularity), 12);
        gd.addChoice("Show:", showStrings, showStrings[showChoice]);

        String[] labels = new String[8];
        boolean[] states = new boolean[8];
        labels[0]="Display results"; states[0] = true;
        labels[1]="Exclude on edges"; states[1]=(options&EXCLUDE_EDGE_PARTICLES)!=0;
        labels[2]="Clear results"; states[2]=(options&CLEAR_WORKSHEET)!=0;
        labels[3]="Include holes"; states[3]=(options&INCLUDE_HOLES)!=0;
        labels[4]="Summarize"; states[4]=(options&DISPLAY_SUMMARY)!=0;
        labels[5]="Record starts"; states[5]=false;
        labels[6]="Add to Manager"; states[6]=(options&ADD_TO_MANAGER)!=0;
        labels[7]="In_situ Show"; states[7]=(options&IN_SITU_SHOW)!=0;
        gd.addCheckboxGroup(2, 4, labels, states);

        gd.addMessage("Morphologycal features", g, Color.magenta);
        gd.addCheckbox("Select all morphologycal", false);
        String[] mFeatures = new String[35];
        boolean[] states1 = new boolean[35];

        mFeatures[0] = "Area"; states1[0] = false;
        mFeatures[1] = "Perimeter"; states1[1] = false;
        mFeatures[2] = "Feret"; states1[2] = false;
        mFeatures[3] = "CenterOfMass"; states1[3] = false;
        mFeatures[4] = "Centroid"; states1[4] = false;
        mFeatures[5] = "Circularity"; states1[5] = false;
        mFeatures[6] = "Rectangularity"; states1[6] = false;
        mFeatures[7] = "Max Radius"; states1[7] = false;
        mFeatures[8] = "Min Radius"; states1[8] = false;
        mFeatures[9] = "Mean Radius"; states1[9] = false;
        mFeatures[10] = "Variance Radius"; states1[10] = false;
        mFeatures[11] = "MBCRadius"; states1[11] = false;
        mFeatures[12] = "AspRatio"; states1[12] = false;
        mFeatures[13] = "Roundness"; states1[13] = false;
        mFeatures[14] = "Diameter EquivArea"; states1[14] = false;
        mFeatures[15] = "Diameter EquivPerimeter"; states1[15] = false;
        mFeatures[16] = "Area EquivEllipse"; states1[16] = false;
        mFeatures[17] = "Compactness"; states1[17] = false;
        mFeatures[18] = "Solidity"; states1[18] = false;
        mFeatures[19] = "Concavity"; states1[19] = false;
        mFeatures[20] = "Convexity"; states1[20] = false;
        mFeatures[21] = "Shape"; states1[21] = false;
        mFeatures[22] = "RFactor"; states1[22] = false;
        mFeatures[23] = "ArBBox"; states1[23] = false;
        mFeatures[24] = "Modification Ratio"; states1[24] = false;
        mFeatures[25] = "Sphericity"; states1[25] = false;
        mFeatures[26] = "Endocarp"; states1[26] = false;
        mFeatures[27] = "IS"; states1[27] = false;
        mFeatures[28] = "DS"; states1[28] = false;
        mFeatures[29] = "ConvexArea"; states1[29] = false;
        mFeatures[30] = "ConvexPerimeter"; states1[30] = false;
        mFeatures[31] = "Jaggedness"; states1[31] = false;
        mFeatures[32] = "Haralick Ratio"; states1[32] = false;
        mFeatures[33] = "Elongation"; states1[33] = false;
        mFeatures[34] = "MinFeret"; states1[34] = false;
        gd.addCheckboxGroup(6, 6, mFeatures, states1);

        if(imp.getType() == ImagePlus.GRAY8 || imp.getType() == ImagePlus.GRAY16 || imp.getType() == ImagePlus.GRAY32) {
            gd.addMessage("Textural features", g, Color.magenta);
            gd.addCheckbox("Select all textural", false);
            String[] tFeatures = new String[14];
            boolean[] states2 = new boolean[14];
            tFeatures[0] = "Kurtosis"; states2[0] = false;
            tFeatures[1] = "Mean"; states2[1] = false;
            tFeatures[2] = "Median"; states2[2] = false;
            tFeatures[3] = "Min_max gray"; states2[3] = false;
            tFeatures[4] = "Mode (gray)"; states2[4] = false;
            tFeatures[5] = "Skewness"; states2[5] = false;
            tFeatures[6] = "Std Deviation"; states2[6] = false;
            tFeatures[7] = "GLCM Features"; states2[7] = false;
            tFeatures[8] = "Entropy"; states2[8] = false;
            tFeatures[9] = "Intensity sum"; states2[9] = false;
            tFeatures[10] = "Square intensity sum"; states2[10] = false;
            tFeatures[11] = "Uniformity"; states2[11] = false;
            tFeatures[12] = "Smoothness R"; states2[12] = false;
            tFeatures[13] = "Intensity Std Deviation"; states2[13] = false;
            gd.addCheckboxGroup(3, 5, tFeatures, states2);
        }

        if (imp.getType() == ImagePlus.COLOR_RGB) {
            gd.addMessage("Color features", g, Color.magenta);
            gd.addCheckbox("Select all color", false);
            String[] cFeatures = new String[14];
            boolean[] states3 = new boolean[14];
            cFeatures[0] = "Average Red color";
            states3[0] = false;
            cFeatures[1] = "Average Green color";
            states3[1] = false;
            cFeatures[2] = "Average Blue color";
            states3[2] = false;
            cFeatures[3] = "Red color std deviation";
            states3[3] = false;
            cFeatures[4] = "Green color std deviation";
            states3[4] = false;
            cFeatures[5] = "Blue color std deviation";
            states3[5] = false;
            cFeatures[6] = "Average RGB colors";
            states3[6] = false;
            cFeatures[7] = "SQRT mean value R, G, B";
            states3[7] = false;
            cFeatures[8] = "Average Hue color";
            states3[8] = false;
            cFeatures[9] = "RAverage Saturation color";
            states3[9] = false;
            cFeatures[10] = "Average Intensity color";
            states3[10] = false;
            cFeatures[11] = "Hue color std deviation";
            states3[11] = false;
            cFeatures[12] = "Saturation color std deviation";
            states3[12] = false;
            cFeatures[13] = "Intensity color std deviation";
            states3[13] = false;
            gd.addCheckboxGroup(3, 6, cFeatures, states3);
        }
        gd.addHelp(IJ.URL+"/docs/menus/analyze.html#ap");
        gd.showDialog();
        if (gd.wasCanceled())
            return false;

        gd.setSmartRecording(minSize==0.0&&maxSize==Double.POSITIVE_INFINITY);
        String size = gd.getNextString(); // min-max size
        if (scaled)
            pixelUnits = gd.getNextBoolean();
        if (pixelUnits)
            unitSquared = 1.0;
        else
            unitSquared = cal.pixelWidth*cal.pixelHeight;
        String[] minAndMax = Tools.split(size, " -");
        double mins = minAndMax.length>=1?gd.parseDouble(minAndMax[0]):0.0;
        double maxs = minAndMax.length==2?gd.parseDouble(minAndMax[1]):Double.NaN;
        minSize = Double.isNaN(mins)?DEFAULT_MIN_SIZE:mins/unitSquared;
        maxSize = Double.isNaN(maxs)?DEFAULT_MAX_SIZE:maxs/unitSquared;
        if (minSize<DEFAULT_MIN_SIZE) minSize = DEFAULT_MIN_SIZE;
        if (maxSize<minSize) maxSize = DEFAULT_MAX_SIZE;
        staticMinSize = minSize;
        staticMaxSize = maxSize;

        gd.setSmartRecording(minCircularity==0.0&&maxCircularity==1.0);
        minAndMax = Tools.split(gd.getNextString(), " -"); // min-max circularity
        double minc = minAndMax.length>=1?gd.parseDouble(minAndMax[0]):0.0;
        double maxc = minAndMax.length==2?gd.parseDouble(minAndMax[1]):Double.NaN;
        minCircularity = Double.isNaN(minc)?0.0:minc;
        maxCircularity = Double.isNaN(maxc)?1.0:maxc;
        if (minCircularity<0.0) minCircularity = 0.0;
        if (minCircularity>maxCircularity && maxCircularity==1.0) minCircularity = 0.0;
        if (minCircularity>maxCircularity) minCircularity = maxCircularity;
        if (maxCircularity<minCircularity) maxCircularity = minCircularity;
        if (minCircularity==1.0 && maxCircularity==1.0) minCircularity = 0.0;
        staticMinCircularity = minCircularity;
        staticMaxCircularity = maxCircularity;

        if (gd.invalidNumber()) {
            //IJ.error("Bins invalid.");
            canceled = true;
            return false;
        }
        gd.setSmartRecording(showChoice==0);
        showChoice = gd.getNextChoiceIndex();
        gd.setSmartRecording(false);
        staticShowChoice = showChoice;
        if (gd.getNextBoolean())
            options |= SHOW_RESULTS; else options &= ~SHOW_RESULTS;
        if (gd.getNextBoolean())
            options |= EXCLUDE_EDGE_PARTICLES; else options &= ~EXCLUDE_EDGE_PARTICLES;
        if (gd.getNextBoolean())
            options |= CLEAR_WORKSHEET; else options &= ~CLEAR_WORKSHEET;
        if (gd.getNextBoolean())
            options |= INCLUDE_HOLES; else options &= ~INCLUDE_HOLES;
        if (gd.getNextBoolean())
            options |= DISPLAY_SUMMARY; else options &= ~DISPLAY_SUMMARY;
        if (gd.getNextBoolean())
            options |= RECORD_STARTS; else options &= ~RECORD_STARTS;
        if (gd.getNextBoolean())
            options |= ADD_TO_MANAGER; else options &= ~ADD_TO_MANAGER;
        if (gd.getNextBoolean())
            options |= IN_SITU_SHOW; else options &= ~IN_SITU_SHOW;
        staticOptions = options;
        options |= SHOW_PROGRESS;

        boolean allMorpho = gd.getNextBoolean();
        if(allMorpho) {
            for (i = 0; i < states1.length; i++) {
                states1[i] = true;
                nextMeasure = gd.getNextBoolean();
            }
        }

        doArea = gd.getNextBoolean();
        doPerimeter = gd.getNextBoolean();
        doFeret = gd.getNextBoolean();
        doCenterOfMass = gd.getNextBoolean();
        doCentroid = gd.getNextBoolean();
        doCircularity = gd.getNextBoolean();
        doRectangularity = gd.getNextBoolean();

        numbOfSpaces = 29;
        for(i = 0; i < numbOfSpaces; i++)
            flagb = gd.getNextBoolean();

        doKurtosis = gd.getNextBoolean();
        doMean = gd.getNextBoolean();
        doMedian = gd.getNextBoolean();
        doMinMax = gd.getNextBoolean();
        doMode = gd.getNextBoolean();
        doSkewness = gd.getNextBoolean();
        doStdDev = gd.getNextBoolean();

        if ((options&DISPLAY_SUMMARY)!=0)
            Analyzer.setMeasurements(Analyzer.getMeasurements()|AREA);
        return true;
    }

    private boolean isThresholdedRGB(ImagePlus imp) {
        Object obj = imp.getProperty("Mask");
        if (obj==null || !(obj instanceof ImageProcessor))
            return false;
        ImageProcessor mask = (ImageProcessor)obj;
        return mask.getWidth()==imp.getWidth() && mask.getHeight()==imp.getHeight();
    }

    boolean updateMacroOptions() {
        String options = Macro.getOptions();
        options = options.replace("show=[Overlay Outlines]", "show=Overlay");
        Macro.setOptions(options);
        int index = options.indexOf("maximum=");
        if (index==-1)
            return false;
        index +=8;
        int len = options.length();
        while (index<len-1 && options.charAt(index)!=' ')
            index++;
        if (index==len-1)
            return false;
        int min = (int)Tools.parseDouble(Macro.getValue(options, "minimum", "1"));
        int max = (int)Tools.parseDouble(Macro.getValue(options, "maximum", "999999"));
        options = "size="+min+"-"+max+options.substring(index, len);
        Macro.setOptions(options);
        return true;
    }

    /** Performs particle analysis on the specified image. Returns
     false if there is an error. */
    public boolean analyze(ImagePlus imp) {
        return analyze(imp, imp.getProcessor());
    }

    /** Performs particle analysis on the specified ImagePlus and
     ImageProcessor. Returns false if there is an error. */
    public boolean analyze(ImagePlus imp, ImageProcessor ip) {
        if (this.imp==null) this.imp = imp;
        showResults = (options&SHOW_RESULTS)!=0;
        excludeEdgeParticles = (options&EXCLUDE_EDGE_PARTICLES)!=0;
        resetCounter = (options&CLEAR_WORKSHEET)!=0;
        showProgress = (options&SHOW_PROGRESS)!=0;
        floodFill = (options&INCLUDE_HOLES)==0;
        recordStarts = (options&RECORD_STARTS)!=0;
        addToManager = (options&ADD_TO_MANAGER)!=0;
        if (staticRoiManager!=null) {
            addToManager = true;
            roiManager = staticRoiManager;
            staticRoiManager = null;
        }
        hyperstack = imp.isHyperStack();
        if (staticResultsTable!=null) {
            rt = staticResultsTable;
            staticResultsTable = null;
            showResultsWindow = false;
        }
        displaySummary = (options&DISPLAY_SUMMARY)!=0 ||  (options&SHOW_SUMMARY)!=0;
        inSituShow = (options&IN_SITU_SHOW)!=0;
        outputImage = null;
        ip.snapshot();
        ip.setProgressBar(null);
        if (Analyzer.isRedirectImage()) {
            redirectImp = Analyzer.getRedirectImage(imp);
            if (redirectImp==null) return false;
            int depth = redirectImp.getStackSize();
            if (depth>1 && depth==imp.getStackSize()) {
                ImageStack redirectStack = redirectImp.getStack();
                redirectIP = redirectStack.getProcessor(imp.getCurrentSlice());
            } else
                redirectIP = redirectImp.getProcessor();
        } else if (imp.getType()==ImagePlus.COLOR_RGB) {
            ImagePlus original = (ImagePlus)imp.getProperty("OriginalImage");
            if (original!=null && original.getWidth()==imp.getWidth() && original.getHeight()==imp.getHeight()) {
                redirectImp = original;
                redirectIP = original.getProcessor();
            }
        }

        if (!setThresholdLevels(imp, ip))
            return false;
        width = ip.getWidth();
        height = ip.getHeight();
        if (!(showChoice==NOTHING||showChoice==OVERLAY_OUTLINES||showChoice==OVERLAY_MASKS)) {
            blackBackground = Prefs.blackBackground && inSituShow;
            if (slice==1)
                outlines = new ImageStack(width, height);
            if (showChoice==ROI_MASKS)
                drawIP = new ShortProcessor(width, height);
            else
                drawIP = new ByteProcessor(width, height);
            drawIP.setLineWidth(lineWidth);
            if (showChoice==ROI_MASKS)
            {} // Place holder for now...
            else if (showChoice==MASKS&&!blackBackground)
                drawIP.invertLut();
            else if (showChoice==OUTLINES) {
                if (!inSituShow) {
                    if (customLut==null)
                        makeCustomLut();
                    drawIP.setColorModel(customLut);
                }
                drawIP.setFont(new Font("SansSerif", Font.PLAIN, fontSize));
                if (fontSize>12 && inSituShow)
                    drawIP.setAntialiasedText(true);
            }
            outlines.addSlice(null, drawIP);

            if (showChoice==ROI_MASKS || blackBackground) {
                drawIP.setColor(Color.black);
                drawIP.fill();
                drawIP.setColor(Color.white);
            } else {
                drawIP.setColor(Color.white);
                drawIP.fill();
                drawIP.setColor(Color.black);
            }
        }
        calibration = redirectImp!=null?redirectImp.getCalibration():imp.getCalibration();

        if (measurements==0)
            measurements = Analyzer.getMeasurements();
        measurements &= ~LIMIT;  // ignore "Limit to Threshold"
        if (rt==null) {
            Frame table = WindowManager.getFrame("Seeds Analysis: Results");
            rt = new ResultsTable();
        }
        if(!doArea) measurements -= AREA;
        if(!doPerimeter) measurements -= PERIMETER;
        if(!doFeret) measurements -= FERET;
        if(!doCenterOfMass) measurements -= CENTER_OF_MASS;
        if(!doCircularity) measurements -= CIRCULARITY;
        if(!doRectangularity) measurements -= RECT;
        if(!doKurtosis) measurements -= KURTOSIS;
        if(!doMean) measurements -= MEAN;
        if(!doMedian) measurements -= MEDIAN;
        if(!doMinMax) measurements -= MIN_MAX;
        if(!doMode) measurements -= MODE;
        if(!doSkewness) measurements -= SKEWNESS;
        if(!doStdDev) measurements -= STD_DEV;

        measurements -= (STACK_POSITION+SLICE+SHAPE_DESCRIPTORS+SCIENTIFIC_NOTATION+AREA_FRACTION+ELLIPSE+INTEGRATED_DENSITY+INVERT_Y+
                LIMIT+MAX_STANDARDS+CENTROID);
        analyzer = new Analyzer(imp, measurements, rt);
        if (resetCounter && slice==1 && rt.size()>0) {
            if (!Analyzer.resetCounter())
                return false;
        }
        beginningCount = Analyzer.getCounter();

        byte[] pixels = null;
        if (ip instanceof ByteProcessor)
            pixels = (byte[])ip.getPixels();
        if (r==null) {
            r = ip.getRoi();
            mask = ip.getMask();
            if (displaySummary) {
                if (mask!=null)
                    totalArea = ImageStatistics.getStatistics(ip, AREA, calibration).area;
                else
                    totalArea = r.width*calibration.pixelWidth*r.height*calibration.pixelHeight;
            }
        }
        minX=r.x; maxX=r.x+r.width; minY=r.y; maxY=r.y+r.height;
        if (r.width<width || r.height<height || mask!=null) {
            if (!eraseOutsideRoi(ip, r, mask)) return false;
        }
        int offset;
        double value;
        int inc = Math.max(r.height/25, 1);
        int mi = 0;
        ImageWindow win = imp.getWindow();
        if (win!=null)
            win.running = true;
        if (showChoice==ELLIPSES)
            measurements |= ELLIPSE;
        roiNeedsImage = (measurements&PERIMETER)!=0 || (measurements&SHAPE_DESCRIPTORS)!=0 || (measurements&FERET)!=0;
        particleCount = 0;
        wand = new Wand(ip);
        pf = new PolygonFiller();
        if (floodFill) {
            ImageProcessor ipf = ip.duplicate();
            ipf.setValue(fillColor);
            ff = new FloodFiller(ipf);
        }
        roiType = Wand.allPoints()?Roi.FREEROI:Roi.TRACED_ROI;

        boolean done = false;
        for (int y=r.y; y<(r.y+r.height); y++) {
            offset = y*width;
            for (int x=r.x; x<(r.x+r.width); x++) {
                if (pixels!=null)
                    value = pixels[offset+x]&255;
                else if (imageType==SHORT)
                    value = ip.getPixel(x, y);
                else
                    value = ip.getPixelValue(x, y);
                if (value>=level1 && value<=level2 && !done) {
                    analyzeParticle(x, y, imp, ip);
                    done = level1==0.0&&level2==255.0&&imp.getBitDepth()==8;
                }
            }
            if (showProgress && ((y%inc)==0))
                IJ.showProgress((double)(y-r.y)/r.height);
            if (win!=null)
                canceled = !win.running;
            if (canceled) {
                Macro.abort();
                break;
            }
        }
        if (showProgress)
            IJ.showProgress(1.0);
        if (showResults && showResultsWindow) //&& rt.size()>0)
            rt.updateResults();
        imp.deleteRoi();
        ip.resetRoi();
        ip.reset();
       /* if (displaySummary && IJ.getInstance()!=null)
            updateSliceSummary();*/
        if (addToManager && roiManager!=null)
            roiManager.setEditMode(imp, true);
        maxParticleCount = (particleCount > maxParticleCount) ? particleCount : maxParticleCount;
        totalCount += particleCount;
        if (!canceled)
            showResults();
        return true;
    }

    public double distance(int x1, int y1, int x2, int y2) {
        return Math.abs(Math.sqrt(Math.pow((x2 - x1), 2) + Math.pow((y2 - y1),2)));
    }

    private double getArea(Polygon p) {
        if (p == null) return Double.NaN;
        int carea = 0;
        int iminus1;

        for (int i = 0; i < p.npoints; i++) {
            iminus1 = i - 1;
            if (iminus1 < 0) iminus1 = p.npoints - 1;
            carea += (p.xpoints[i] + p.xpoints[iminus1]) * (p.ypoints[i] - p.ypoints[iminus1]);
        }
        return (Math.abs(carea / 2.0));
    } //mio

    /*Riguardante ConvexHull-
     * Calcolo del perimetro dato i punti del poligono e calcolando le distanze tra i punti*/
    private final double getPerimeter(Polygon p) {
        if (p == null) return Double.NaN;

        double cperimeter = 0.0;
        int iminus1;

        for (int i = 0; i < p.npoints; i++) {
            iminus1 = i - 1;
            if (iminus1 < 0) iminus1 = p.npoints - 1;
            cperimeter += distance(p.xpoints[i], p.ypoints[i], p.xpoints[iminus1], p.ypoints[iminus1]);
        }
        return cperimeter;
    } //mio


    private int[] getIS(Roi roi){
        int impHeight = imp.getHeight();
        int impWidth = imp.getWidth();
        Rectangle r = roi.getBounds();
        int bbCenterX = r.x + r.width/2;
        int bbCenterY = impHeight - r.y - r.height/2;
        int[] IS = new int[2];
        IS[0] = bbCenterX;
        IS[1] = bbCenterY;
        return IS;

    }

    //Distance between IS and CG
    private double getDS(Roi roi, int[] is, double x_cg, double y_cg){
        //double ds = Math.sqrt(Math.pow((is[0] - x_cg), 2.0) + Math.pow((is[1] - y_cg), 2.0));
        Point2D.Double pIs = new Point2D.Double(is[0], is[1]);
        Point2D.Double pCg = new Point2D.Double(x_cg, y_cg);
        double ds = pIs.distance(pCg);
        return ds;
    }

    private double[] getRadiiValues(Roi roi, double x_cg, double y_cg){
        Polygon p = roi.getPolygon();
        int n = p.npoints;
        int i;
        int impHeight = imp.getHeight();
        double sumR = 0;
        double variance = 0;
        double[] radii = new double[n];
        double[] radiiValues = new double[5]; //minR, maxR, media, variance, stdDev
        radiiValues[0] = Double.MAX_VALUE; //min
        radiiValues[1] = -1; //max

        for(i = 0; i < n; i++){
            radii[i] = distance((int)x_cg, (int)y_cg, p.xpoints[i],impHeight -p.ypoints[i]);

            if(radii[i] < radiiValues[0])
                radiiValues[0] = radii[i];
            if(radii[i] > radiiValues[1])
                radiiValues[1] = radii[i];
            sumR+= radii[i];
        }

        double media = sumR/n;
        radiiValues[2] = media;

        for(i = 0; i < n; i++){
            variance += (radii[i] - media) * (radii[i] - media);
        }
        variance /= (n - 1);
        radiiValues[3] = variance;
        radiiValues[4] = Math.sqrt(variance); //std deviation
        return  radiiValues;
    }
    void updateSliceSummary() {
        int slices = imp.getStackSize();
        if (slices==1) {
            Frame frame = WindowManager.getFrame("Summary");
            if (frame!=null && (frame instanceof TextWindow)) {
                TextWindow tw = (TextWindow)frame;
                ResultsTable table = tw.getTextPanel().getResultsTable();
                if (table!= null)
                    summaryTable = table;
            }
        } else {
            Frame frame = WindowManager.getFrame("Summary of "+imp.getTitle());
            if (frame!=null && (frame instanceof TextWindow)) {
                TextWindow tw = (TextWindow)frame;
                ResultsTable table = tw.getTextPanel().getResultsTable();
                if (table!= null)
                    summaryTable = table;
            }
        }
        if (summaryTable==null)
            summaryTable = new ResultsTable();
        float[] areas = rt.getColumn(ResultsTable.AREA);
        if (areas==null)
            areas = new float[0];
        String label = imp.getTitle();
        if (slices>1) {
            if (processStack)
                label = imp.getStack().getShortSliceLabel(slice);
            else
                label = imp.getStack().getShortSliceLabel(imp.getCurrentSlice());
            label = label!=null&&!label.equals("")?label:""+slice;
        }
        summaryTable.incrementCounter();
        summaryTable.addValue("Slice", label);

        double sum = 0.0;
        int start = areas.length-particleCount;
        if (start<0)
            return;
        for (int i=start; i<areas.length; i++)
            sum += areas[i];
        int places = Analyzer.getPrecision();
        Calibration cal = imp.getCalibration();
        summaryTable.addValue("Count", particleCount);
        summaryTable.addValue("Total Area", sum);
        summaryTable.addValue("Average Size", sum/particleCount);
        summaryTable.addValue("%Area", sum*100.0/totalArea);
        addMeans(areas.length>0?start:-1);
        String title = slices==1?"Summary":"Summary of "+imp.getTitle();//Summary
        summaryTable.show(title);
    }

    private double getEntropy(int[] hist, double area) {
        double sum = 0.0;
        for (int i = 0; i < hist.length; i++) {
            if (hist[i] != 0) sum += (double) (hist[i] / area) * log2((double) (hist[i] / area));
        }

        return -sum;
    }

    private int getIntensitySum(int[] hist) {
        int sum = 0;
        for (int i = 0; i < hist.length; i++) {
            sum += hist[i];
        }
        return sum;
    }

    private int getSquareIntensitySum(int[] hist) {
        int sum = 0;
        for (int i = 0; i < hist.length; i++) {
            sum += Math.pow(hist[i],2);
        }
        return sum;
    }

    private double getUniformity(int[] hist, double area) {
        double uniformity = 0.0;

        for (int i = 0; i < hist.length; i++) {
            uniformity += Math.pow(((double) hist[i] / area), 2);
        }

        return uniformity;
    }

    private double getSmoothness(double variance) {
        //the variance in this measure is normalized to the rage [0, 1] by dividing it by (L-1)^2
        //L --> grey level

        //only grey level in the object or in the histagram?
        int greyLevel = 256;

        double varianceNormalized = variance / Math.pow(greyLevel - 1, 2);

        return 1 - (1 / (1 + varianceNormalized));
    }

    private int[] minMax(int[] hist){
        int max = 0;
        int min = 255;

        for(int i = 0; i < hist.length; i++){
            if(hist[i] < min)
                min = hist[i];
            if(hist[i] > max)
                max = hist[i];
        }

        int[] mm = new int[2];
        mm[0] = min;
        mm[1] = max;

        return mm;
    }

    private ImagePlus [] getHSIImagePluses(ImagePlus imp){
        ImagePlus [] HSIimp = new ImagePlus[3];
        int w = imp.getWidth();
        int h = imp.getHeight();

        ImageStack hsiStack = imp.getStack();
        ImageStack hueStack = new ImageStack(w,h);
        ImageStack satStack = new ImageStack(w,h);
        ImageStack intStack = new ImageStack(w,h);

        byte[] hue,s,in;

        ColorProcessor cp;
        int n = hsiStack.getSize();

        for (int i=1; i<=n; i++) {
            hue = new byte[w*h];
            s = new byte[w*h];
            in = new byte[w*h];
            cp = (ColorProcessor)hsiStack.getProcessor(1);
            cp.getHSB(hue,s,in);
            hueStack.addSlice(null,hue);
            satStack.addSlice(null,s);
            intStack.addSlice(null,in);
        }

        HSIimp[0] = new ImagePlus("hue", hueStack);
        HSIimp[1] = new ImagePlus("sat", satStack);
        HSIimp[2] = new ImagePlus("int", intStack);

        return HSIimp;
    }

    public double log2(double d) {
        return Math.log(d)/Math.log(2.0);
    }
    // glcm.GLCMTexture.java v0.011
    // Writed by Angel Zeitoune, based on previews versions

    public void calcGLCM(ImageProcessor ip) {
        // use the bounding rectangle ROI to roughly limit processing
        Rectangle roi = ip.getRoi();
        int pixelOffset = 1;             // step (displacement or distance) between reference and the neighbour pixel
        int phi = 0;                     // Angle
        // get byte arrays for the image pixels and mask pixels
        int width = ip.getWidth();      // window width

        byte[] pixels = (byte[]) ip.getPixels();
        byte[] mask = ip.getMaskArray();

        double pixelCount = 0;

        double rad = Math.toRadians(-1.0 * phi);
        int offsetX = (int) (pixelOffset * Math.round(Math.cos(rad)));
        int offsetY = (int) (pixelOffset * Math.round(Math.sin(rad)));
        //IJ.log("Angle: " + phi + " - offset X: " + offsetX + " - offset Y: " + offsetY );

        int value;      // value at pixel of interest
        int dValue;     // value of pixel at offset
        glcm = new double[256][256];   // GLCM matrix. Only for 8-bit images

        // loop through the pixels in the ROI bounding rectangle
        for (int y = roi.y; y < (roi.y + roi.height); y++) {
            for (int x = roi.x; x < (roi.x + roi.width); x++) {
                // check to see if the pixel is in the mask (if it exists)
                if ((mask == null) || ((0xff & mask[(((y - roi.y) * roi.width) + (x - roi.x))]) > 0)) {
                    // check to see if the offset pixel is in the roi
                    int dx = x + offsetX;
                    int dy = y + offsetY;
                    if (((dx >= roi.x) && (dx < (roi.x + roi.width))) && ((dy >= roi.y) && (dy < (roi.y + roi.height)))) {
                        // check to see if the offset pixel is in the mask (if it exists)
                        if ((mask == null) || ((0xff & mask[(((dy - roi.y) * roi.width) + (dx - roi.x))]) > 0)) {
                            value = 0xff & pixels[(y * width) + x];
                            dValue = 0xff & pixels[(dy * width) + dx];
                            glcm[value][dValue]++;
                            pixelCount++;
                        }
                    }

                    // symmetry, invert the offsets and go through the process again

                    dx = x - offsetX;
                    dy = y - offsetY;
                    if (((dx >= roi.x) && (dx < (roi.x + roi.width))) && ((dy >= roi.y) && (dy < (roi.y + roi.height)))) {
                        // check to see if the offset pixel is in the mask (if it exists)
                        if ((mask == null) || ((0xff & mask[(((dy - roi.y) * roi.width) + (dx - roi.x))]) > 0)) {
                            value = 0xff & pixels[(y * width) + x];
                            dValue = 0xff & pixels[(dy * width) + dx];
                            glcm[dValue][value]++;
                            pixelCount++;
                        }
                    }

                }
            }
        }

        double [] px = new double [256];
        double [] py = new double [256];
        double meanx=0.0;
        double meany=0.0;
        double stdevx=0.0;
        double stdevy=0.0;

        // Px(i) and Py(j) are the marginal-probability matrix; sum rows (px) or columns (py)
        // First, initialize the arrays to 0
        for (int i=0;  i<256; i++){
            px[i] = 0.0;
            py[i] = 0.0;

        /*meanx1[i] = 0.0;
        meany1[i] = 0.0;
        varianceX[i] = 0.0;
        varianceY[i] = 0.0;*/
        }

        // sum the glcm rows to Px(i)
        for (int i=0;  i<256; i++) {
            for (int j=0; j<256; j++) {
                px[i] += glcm [i][j];
            }
            //meanx1[i] = i*px[i];
            //IJ.log("meanx1 : " + meanx1[i]);
        }

        // sum the glcm rows to Py(j)
        for (int j=0;  j<256; j++) {
            for (int i=0; i<256; i++) {
                py[j] += glcm [i][j];
            }
            //meany1[j] = j*py[j];
            //IJ.log("meany1 : " + meany1[j]);
        }

        // calculate meanx and meany
        for (int i=0;  i<256; i++) {

            meanx += (i*px[i]);
            meany += (i*py[i]);
        }

        // calculate stdevx and stdevy
        for (int i=0;  i<256; i++) {
            stdevx += ((i-meanx)*(i-meanx)*px[i]);
            stdevy += ((i-meany)*(i-meany)*py[i]);

            //varianceX[i] += ((i-meanx1[i])*(i-meanx1[i])*py[i]);
            //varianceY[i] += ((i-meany1[i])*(i-meany1[i])*px[i]);

            //IJ.log("varianceX: " + varianceX[i]);
            //IJ.log("varianceY: " + varianceY[i]);
        }

        double asm = 0.0;
        for(int i = 0;  i<256; i++)  {
            for (int j=0; j<256; j++) {
                asm += (glcm[i][j]*glcm[i][j]);
            }
        }

        //===============================================================================================
        // calculate the inverse difference moment (idm) (Walker, et al. 1995)
        // this is calculated using the same formula as Conners, et al., 1984 "Local Homogeneity"
        // (formula 15.40, Bankman, 2009)

        double IDM = 0.0;
        for (int i=0;  i<256; i++)  {
            for (int j=0; j<256; j++) {
                IDM += ((1/(1+(Math.pow(i-j,2))))*glcm[i][j]);
            }
        }



        //===============================================================================================
        // (formula 15.39, Bankman, 2009) energy weighted by pixel value difference

        double contrast=0.0;

        for (int i=0;  i<256; i++)  {
            for (int j=0; j<256; j++) {
                contrast += ((i-j)*(i-j) * (glcm[i][j]));
            }
        }


        //===============================================================================================
        // calculate the energy
        // - same as Angular 2nd Moment (see above), so may be delete this.
        double energy = 0.0;
        for (int i=0;  i<256; i++)  {
            for (int j=0; j<256; j++) {
                energy += Math.pow(glcm[i][j],2);
            }
        }
        //===============================================================================================
        // calculate the entropy (Haralick et al., 1973; Walker, et al., 1995)

        double entropy = 0.0;
        for (int i=0;  i<256; i++)  {
            for (int j=0; j<256; j++) {
                if (glcm[i][j] != 0) {
                    //entropy = entropy-(glcm[i][j]*(Math.log(glcm[i][j])));
                    //the next line is how Xite calculates it -- I am not sure why they use this, I do not think it is correct
                    //(they also use log base 10, which I need to implement)
                    entropy = entropy-(glcm[i][j]*((Math.log(glcm[i][j]))/Math.log(2.0)) );
                }
            }
        }

        // calculate the homogeneity (Parker)
        // "Local Homogeneity" from Conners, et al., 1984 is calculated the same as IDM above
        // Parker's implementation is below; absolute value of i-j is taken rather than square
        // - matlab textbook also uses non-squred absolute difference |i-j|
        // -- using absolute value, flat image (diagonal) will be 1.
        double homogeneity = 0.0;
        for (int i=0;  i<256; i++) {
            for (int j=0; j<256; j++) {
                homogeneity += glcm[i][j]/(1.0+Math.abs(i-j));
            }
        }

        //===============================================================================================
        // calculate the variance ("variance" in Walker 1995; "Sum of Squares: Variance" in Haralick 1973)

        double variance = 0.0;
        double mean = 0.0;

        mean = (meanx + meany)/2;

        for (int i=0;  i<256; i++){
            for (int j = 0; j < 256; j++) {
                variance += (Math.pow((i - mean), 2) * glcm[i][j]);
            }
        }
        /** Shade
         * calculate the shade (Walker, et al., 1995; Connors, et al. 1984)
         */
        double shade = 0.0;

        // calculate the shade parameter
        for (int i=0;  i<256; i++) {
            for (int j=0; j<256; j++) {
                shade += (Math.pow((i+j-meanx-meany),3)*glcm[i][j]);
            }
        }


        //==============================================================================================
        // calculate the prominence (Walker, et al., 1995; Connors, et al. 1984
        double prominence=0.0;

        for (int i=0;  i<256; i++) {
            for (int j=0; j<256; j++) {
                prominence += (Math.pow((i+j-meanx-meany),4)*glcm[i][j]);
            }
        }

        //===============================================================================================
        // calculate the inertia (Walker, et al., 1995; Connors, et al. 1984)
        double inertia = 0.0;
        for (int i=0;  i<256; i++)  {
            for (int j=0; j<256; j++) {
                if (glcm[i][j] != 0) {
                    inertia += (Math.pow((i-j),2)*glcm[i][j]);
                }
            }
        }

        //=====================================================================================================
        /** calculate the correlation
         *  methods based on Haralick 1973 (and MatLab), Walker 1995 are included below
         * Haralick/Matlab result reported for correlation currently; will give Walker as an option in the future
         */
        double correlation=0.0;

        // calculate the correlation parameter
        for (int i=0;  i<256; i++) {
            for (int j=0; j<256; j++) {
                correlation += (((i - meanx) * (j - meany)) * glcm[i][j]);

            }
        }
        correlation /= Math.sqrt(stdevx * stdevy);


        //===============================================================================================
        // calculate the sum of all glcm elements

        double sum = 0.0;
        for (int i=0; i<256; i++)  {
            for (int j=0; j<256; j++) {
                sum = sum + glcm[i][j];
            }
        }
        // convert the GLCM from absolute counts to probabilities
        for (int i = 0; i < 256; i++) {
            for (int j = 0; j < 256; j++) {
                glcm[i][j] = (glcm[i][j]) / (pixelCount);
            }
        }
        IJ.showMessage("GLCM and Moments", "Contrast: "+(double)Math.round(contrast * 100000d) / 100000d+"\n"
                + "Correlation: "+(double)Math.round(correlation * 100000d) / 100000d+"\n"
                + "Entropy: "+(double)Math.round(entropy * 100000d) / 100000d+"\n"
                + "Inertia: "+(double)Math.round(inertia * 100000d) / 100000d+"\n"
                + "Prominence: "+(double)Math.round(prominence * 100000d) / 100000d+"\n"
                + "Shade: "+(double)Math.round(shade * 100000d) / 100000d+"\n"
                + "Homogeneity: "+(double)Math.round(homogeneity * 100000d) / 100000d+"\n"
                + "Energy: "+(double)Math.round(energy * 100000d) / 100000d+"\n"
                + "Sum of squares (variance): "+(double)Math.round(variance * 100000d) / 100000d+"\n"
                + "Sum all GLCM elements: "+(double)Math.round(sum * 100000d) / 100000d+"\n"
                + "Inverse different moment: "+(double)Math.round(IDM * 100000d) / 100000d+"\n"
                + "Angular second moment: "+(double)Math.round(asm * 100000d) / 100000d+"\n");
    }

    void addMeans(int start) {
        if ((measurements&MEAN)!=0) addMean(ResultsTable.MEAN, start);
        if ((measurements&MODE)!=0) addMean(ResultsTable.MODE, start);
        if ((measurements&PERIMETER)!=0)
            addMean(ResultsTable.PERIMETER, start);
        if ((measurements&ELLIPSE)!=0) {
            addMean(ResultsTable.MAJOR, start);
            addMean(ResultsTable.MINOR, start);
            addMean(ResultsTable.ANGLE, start);
        }
        if ((measurements&SHAPE_DESCRIPTORS)!=0) {
            addMean(ResultsTable.CIRCULARITY, start);
            addMean(ResultsTable.SOLIDITY, start);
        }
        if ((measurements&FERET)!=0) {
            addMean(ResultsTable.FERET, start);
            addMean(ResultsTable.FERET_X, start);
            addMean(ResultsTable.FERET_Y, start);
            addMean(ResultsTable.FERET_ANGLE, start);
            addMean(ResultsTable.MIN_FERET, start);
        }
        if ((measurements&INTEGRATED_DENSITY)!=0)
            addMean(ResultsTable.INTEGRATED_DENSITY, start);
        if ((measurements&MEDIAN)!=0)
            addMean(ResultsTable.MEDIAN, start);
        if ((measurements&SKEWNESS)!=0)
            addMean(ResultsTable.SKEWNESS, start);
        if ((measurements&KURTOSIS)!=0)
            addMean(ResultsTable.KURTOSIS, start);
    }

    private void addMean(int column, int start) {
        double value = Double.NaN;
        if (start!=-1) {
            float[] c = column>=0?rt.getColumn(column):null;
            if (c!=null) {
                ImageProcessor ip = new FloatProcessor(c.length, 1, c, null);
                if (ip==null) return;
                ip.setRoi(start, 0, ip.getWidth()-start, 1);
                ip = ip.crop();
                ImageStatistics stats = new FloatStatistics(ip);
                if (stats==null)
                    return;
                value = stats.mean;
            }
        }
        summaryTable.addValue(ResultsTable.getDefaultHeading(column), value);
    }

    boolean eraseOutsideRoi(ImageProcessor ip, Rectangle r, ImageProcessor mask) {
        int width = ip.getWidth();
        int height = ip.getHeight();
        ip.setRoi(r);
        if (excludeEdgeParticles && polygon!=null) {
            ImageStatistics stats = ImageStatistics.getStatistics(ip);//prova. Era: getStatistics(ip,AREA+KURT,null)
            if (fillColor>=stats.min && fillColor<=stats.max) {
                double replaceColor = level1-1.0;
                if (replaceColor<0.0 || replaceColor==fillColor) {
                    replaceColor = level2+1.0;
                    int maxColor = imageType==BYTE?255:65535;
                    if (replaceColor>maxColor || replaceColor==fillColor) {
                        IJ.error("Particle Analyzer", "Unable to remove edge particles");
                        return false;
                    }
                }
                for (int y=minY; y<maxY; y++) {
                    for (int x=minX; x<maxX; x++) {
                        int v  = ip.getPixel(x, y);
                        if (v==fillColor) ip.putPixel(x, y, (int)replaceColor);
                    }
                }
            }
        }
        ip.setValue(fillColor);
        if (mask!=null) {
            mask = mask.duplicate();
            mask.invert();
            ip.fill(mask);
        }
        ip.setRoi(0, 0, r.x, height);
        ip.fill();
        ip.setRoi(r.x, 0, r.width, r.y);
        ip.fill();
        ip.setRoi(r.x, r.y+r.height, r.width, height-(r.y+r.height));
        ip.fill();
        ip.setRoi(r.x+r.width, 0, width-(r.x+r.width), height);
        ip.fill();
        ip.resetRoi();
        return true;
    }

    boolean setThresholdLevels(ImagePlus imp, ImageProcessor ip) {
        double t1 = ip.getMinThreshold();
        double t2 = ip.getMaxThreshold();
        boolean invertedLut = imp.isInvertedLut();
        boolean byteImage = ip instanceof ByteProcessor;
        if (ip instanceof ShortProcessor)
            imageType = SHORT;
        else if (ip instanceof FloatProcessor)
            imageType = FLOAT;
        else
            imageType = BYTE;
        if (t1==ImageProcessor.NO_THRESHOLD) {
            noThreshold = true;
            ImageStatistics stats = imp.getStatistics();
            if (imageType!=BYTE || (stats.histogram[0]+stats.histogram[255]!=stats.pixelCount)) {
                IJ.error("Particle Analyzer: seeds",
                        "A thresholded image or 8-bit binary image is\n"
                                +"required. Threshold levels can be set using\n"
                                +"the Image->Adjust->Threshold tool.");
                canceled = true;
                return false;
            }
            boolean threshold255 = invertedLut;
            if (Prefs.blackBackground)
                threshold255 = !threshold255;
            if (threshold255) {
                level1 = 255;
                level2 = 255;
                fillColor = 64;
            } else {
                level1 = 0;
                level2 = 0;
                fillColor = 192;
            }
        } else {
            level1 = t1;
            level2 = t2;
            if (imageType==BYTE) {
                if (level1>0)
                    fillColor = 0;
                else if (level2<255)
                    fillColor = 255;
            } else if (imageType==SHORT) {
                if (level1>0)
                    fillColor = 0;
                else if (level2<65535)
                    fillColor = 65535;
            } else if (imageType==FLOAT)
                fillColor = -Float.MAX_VALUE;
            else
                return false;
        }
        imageType2 = imageType;
        if (redirectIP!=null) {
            if (redirectIP instanceof ShortProcessor)
                imageType2 = SHORT;
            else if (redirectIP instanceof FloatProcessor)
                imageType2 = FLOAT;
            else if (redirectIP instanceof ColorProcessor)
                imageType2 = RGB;
            else
                imageType2 = BYTE;
        }
        return true;
    }

    int counter = 0;

    void analyzeParticle(int x, int y, ImagePlus imp, ImageProcessor ip) {
        ImageProcessor ip2 = redirectIP!=null?redirectIP:ip;
        wand.autoOutline(x, y, level1, level2, wandMode);
        if (wand.npoints==0)
        {IJ.log("wand error: "+x+" "+y); return;}
        Roi roi = new PolygonRoi(wand.xpoints, wand.ypoints, wand.npoints, roiType);
        Rectangle r = roi.getBounds();
        if (r.width>1 && r.height>1) {
            PolygonRoi proi = (PolygonRoi)roi;
            pf.setPolygon(proi.getXCoordinates(), proi.getYCoordinates(), proi.getNCoordinates());
            ip2.setMask(pf.getMask(r.width, r.height));
            if (floodFill) ff.particleAnalyzerFill(x, y, level1, level2, ip2.getMask(), r);
        }
        ip2.setRoi(r);
        ip.setValue(fillColor);
        ImageStatistics stats = getStatistics(ip2, measurements, calibration);
        boolean include = true;
        if (excludeEdgeParticles) {
            if (r.x==minX||r.y==minY||r.x+r.width==maxX||r.y+r.height==maxY)
                include = false;
            if (polygon!=null) {
                Rectangle bounds = roi.getBounds();
                int x1=bounds.x+wand.xpoints[wand.npoints-1];
                int y1=bounds.y+wand.ypoints[wand.npoints-1];
                int x2, y2;
                for (int i=0; i<wand.npoints; i++) {
                    x2=bounds.x+wand.xpoints[i];
                    y2=bounds.y+wand.ypoints[i];
                    if (!polygon.contains(x2, y2)){
                        include = false;
                        break;
                    }
                    if ((x1==x2 && ip.getPixel(x1,y1-1)==fillColor) || (y1==y2 && ip.getPixel(x1-1,y1)==fillColor)) {
                        include = false;
                        break;
                    }
                    x1=x2; y1=y2;
                }
            }
        }
        ImageProcessor mask = ip2.getMask();
        if (minCircularity>0.0 || maxCircularity!=1.0) {
            double perimeter = roi.getLength();
            double circularity = perimeter==0.0?0.0:4.0*Math.PI*(stats.pixelCount/(perimeter*perimeter));
            if (circularity>1.0 && maxCircularity<=1.0) circularity = 1.0;
            if (circularity<minCircularity || circularity>maxCircularity) include = false;
        }
        if (stats.pixelCount>=minSize && stats.pixelCount<=maxSize && include) {
            particleCount++;
            if (roiNeedsImage)
                roi.setImage(imp);
            stats.xstart=x; stats.ystart=y;
            saveResults(stats, roi);
            if (showChoice!=NOTHING)
                drawParticle(drawIP, roi, stats, mask);
        }
        if (redirectIP!=null)
            ip.setRoi(r);
        ip.fill(mask);


    }

    ImageStatistics getStatistics(ImageProcessor ip, int mOptions, Calibration cal) {
        switch (imageType2) {
            case BYTE:
                return new ByteStatistics(ip, mOptions, cal);
            case SHORT:
                return new ShortStatistics(ip, mOptions, cal);
            case FLOAT:
                return new FloatStatistics(ip, mOptions, cal);
            case RGB:
                return new ColorStatistics(ip, mOptions, cal);
            default:
                return null;
        }
    }

    /** Saves statistics for one particle in a results table. This is
     a method subclasses can override. */
    protected void saveResults(ImageStatistics stats, Roi roi) {
        analyzer.saveResults(stats, roi);
        rt.addLabel("White Apesorgia");
        if (maxCircularity>1.0 && rt.columnExists(rt.getColumnIndex("Circ.")) && rt.getValue("Circ.", rt.size()-1)==1.0) {
            double perimeter = roi.getLength();
            double circularity = perimeter==0.0?0.0:4.0*Math.PI*(stats.pixelCount/(perimeter*perimeter));
            rt.addValue("Circ.", circularity);
        }
        if (recordStarts) {
            rt.addValue("XStart", stats.xstart);
            rt.addValue("YStart", stats.ystart);
        }
        Vector<Checkbox> gdCCheckboxes = this.gd_c.getCheckboxes();

        Polygon polygon = roi.getConvexHull();
        double convexArea = getArea(polygon);
        double convexPerimeter = getPerimeter(polygon);
        double perimeter = roi.getLength();
        double[] feretVector = roi.getFeretValues();
        double arbBox = feretVector[0]*stats.roiWidth;
        double[] radiiValues = getRadiiValues(roi, stats.xCenterOfMass, stats.yCenterOfMass);
        int[] histogram = stats.histogram;
        double variance = Math.pow(stats.stdDev, 2);
        if(imp.getType() == ImagePlus.COLOR_RGB){
            splitRGB[0].setRoi(roi); //red channel
            splitRGB[1].setRoi(roi); //green channel
            splitRGB[2].setRoi(roi); //blue channel

            ImageStatistics statsR = splitRGB[0].getStatistics();
            ImageStatistics statsG = splitRGB[1].getStatistics();
            ImageStatistics statsB = splitRGB[2].getStatistics();

            HSI[0].setRoi(roi); //hue
            HSI[1].setRoi(roi); //saturation
            HSI[2].setRoi(roi); //intensity

            ImageStatistics statsHue = HSI[0].getStatistics();
            ImageStatistics statsSat = HSI[1].getStatistics();
            ImageStatistics statsInt = HSI[2].getStatistics();

            if(gdCCheckboxes.get(45).getState()){

                rt.addValue("Red mean", statsR.mean);
                rt.addValue("Green mean", statsG.mean);
                rt.addValue("Blue mean", statsB.mean);
                rt.addValue("Average RGB colors", (statsR.mean + statsG.mean + statsB.mean)/3);
                rt.addValue("Red mean Sqrt", Math.sqrt(statsR.mean));
                rt.addValue("Green mean Sqrt", Math.sqrt(statsG.mean));
                rt.addValue("Blue mean Sqrt", Math.sqrt(statsB.mean));

                rt.addValue("Red StdDev", statsR.stdDev);
                rt.addValue("Green StdDev", statsG.stdDev);
                rt.addValue("Blue StdDev", statsB.stdDev);

                rt.addValue("Average Hue color", statsHue.mean);
                rt.addValue("Average Saturation color", statsSat.mean);
                rt.addValue("Average Intensity color", statsInt.mean);

                rt.addValue("Hue color stdDev", statsHue.stdDev);
                rt.addValue("Saturation color stdDev", statsSat.stdDev);
                rt.addValue("Intensity color stdDev", statsInt.stdDev);

            }

            if(gdCCheckboxes.get(46).getState()) rt.addValue("Red mean", statsR.mean);
            if(gdCCheckboxes.get(47).getState()) rt.addValue("Green mean", statsG.mean);
            if(gdCCheckboxes.get(48).getState()) rt.addValue("Blue mean", statsB.mean);
            if(gdCCheckboxes.get(49).getState()) rt.addValue("Red StdDev", statsR.stdDev);
            if(gdCCheckboxes.get(50).getState()) rt.addValue("Green StdDev", statsG.stdDev);
            if(gdCCheckboxes.get(51).getState()) rt.addValue("Blue StdDev", statsB.stdDev);
            if(gdCCheckboxes.get(52).getState()) rt.addValue("Average RGB colors", (statsR.mean + statsG.mean + statsB.mean)/3);
            if(gdCCheckboxes.get(53).getState()){
                rt.addValue("Red mean Sqrt", Math.sqrt(statsR.mean));
                rt.addValue("Green mean Sqrt", Math.sqrt(statsG.mean));
                rt.addValue("Blue mean Sqrt", Math.sqrt(statsB.mean));
            }

            if(gdCCheckboxes.get(54).getState()) rt.addValue("Average Hue color", statsHue.mean);
            if(gdCCheckboxes.get(55).getState()) rt.addValue("Average Saturation color", statsSat.mean);
            if(gdCCheckboxes.get(56).getState()) rt.addValue("Average Intensity color", statsInt.mean);

            if(gdCCheckboxes.get(57).getState()) rt.addValue("Hue color stdDev", statsHue.stdDev);
            if(gdCCheckboxes.get(58).getState()) rt.addValue("Saturation color stdDev", statsSat.stdDev);
            if(gdCCheckboxes.get(59).getState()) rt.addValue("Intensity color stdDev", statsInt.stdDev);

        }

        int[] intersectionIS = getIS(roi);
        int[] minMaxGray = minMax(histogram);


        if(gdCCheckboxes.get(9).getState()){

            rt.addValue("Convex Area",convexArea);//convexArea
            rt.addValue("Convex Perimeter", convexPerimeter);//convexPerimeter
            rt.addValue("Centroid: x", stats.xCentroid);
            rt.addValue("Centroid: y", stats.yCentroid);
            rt.addValue("IS: x", intersectionIS[0]);
            rt.addValue("IS: y", intersectionIS[1]);
            rt.addValue("Jaggedness", (2*Math.sqrt(Math.PI*stats.area))/perimeter);
            rt.addValue(ResultsTable.PERIMETER, roi.getLength());
            rt.addValue("DS",getDS(roi, intersectionIS, stats.xCenterOfMass, stats.yCenterOfMass));
            rt.addValue("Compactness", Math.sqrt((4/Math.PI)*stats.area)/feretVector[0]);
            rt.addValue("Concavity", convexArea - stats.area);
            rt.addValue("Convexity",convexPerimeter/perimeter);
            rt.addValue("Shape", Math.pow(perimeter, 2)/stats.area);
            rt.addValue("Solidity", stats.area/convexArea);
            rt.addValue("RFactor", convexArea/(feretVector[0]*Math.PI));
            rt.addValue("ArBBox", arbBox);
            rt.addValue("Rectangularity2", stats.area/arbBox);//vedere, dovrebbe già farlo
            rt.addValue("MinR", radiiValues[0]);
            rt.addValue("MaxR", radiiValues[1]);
            rt.addValue("MeanR", radiiValues[2]);
            rt.addValue("VarianceR", radiiValues[3]);
            rt.addValue("AreaEquivD", Math.sqrt(4/Math.PI) * stats.area);
            rt.addValue("PerEquivD", stats.area/Math.PI);
            rt.addValue("EquivEllAr", (Math.PI * feretVector[0] * stats.roiWidth)/4);
            rt.addValue("ModRatio", (2 * radiiValues[0])/feretVector[0]);
            rt.addValue("Sphericity", radiiValues[0] / radiiValues[1]);// also called radius ratio
            rt.addValue("Endocarp", stats.area - perimeter);
            rt.addValue("Haralick Ratio", radiiValues[2] / radiiValues[4]);
            rt.addValue("Elongation", Math.pow(perimeter, 2)/(4 * Math.PI * stats.area));
            rt.addValue("Min Feret", feretVector[2]);
        }

        if(gdCCheckboxes.get(39).getState()) rt.addValue("Convex Area",convexArea);//convexArea
        if(gdCCheckboxes.get(40).getState()) rt.addValue("Convex Perimeter", convexPerimeter);//convexPerimeter


        if(gdCCheckboxes.get(14).getState()){
            rt.addValue("Centroid: x", stats.xCentroid);
            rt.addValue("Centroid: y", stats.yCentroid);
        }

        if(gdCCheckboxes.get(37).getState()) {
            rt.addValue("IS: x", intersectionIS[0]);
            rt.addValue("IS: y", intersectionIS[1]);
        }
        if(gdCCheckboxes.get(41).getState()) rt.addValue("Jaggedness", (2*Math.sqrt(Math.PI*stats.area))/perimeter);
        if(gdCCheckboxes.get(11).getState()) rt.addValue(ResultsTable.PERIMETER, roi.getLength());
        if(gdCCheckboxes.get(38).getState()) rt.addValue("DS",getDS(roi, intersectionIS, stats.xCenterOfMass, stats.yCenterOfMass));
        if(gdCCheckboxes.get(27).getState()) rt.addValue("Compactness", Math.sqrt((4/Math.PI)*stats.area)/feretVector[0]);
        if(gdCCheckboxes.get(29).getState()) rt.addValue("Concavity", convexArea - stats.area);
        if(gdCCheckboxes.get(30).getState()) rt.addValue("Convexity",convexPerimeter/perimeter);
        if(gdCCheckboxes.get(31).getState()) rt.addValue("Shape", Math.pow(perimeter, 2)/stats.area);
        if(gdCCheckboxes.get(28).getState()) rt.addValue("Solidity", stats.area/convexArea);
        if(gdCCheckboxes.get(32).getState()) rt.addValue("RFactor", convexArea/(feretVector[0]*Math.PI));
        if(gdCCheckboxes.get(33).getState()) rt.addValue("ArBBox", arbBox);
        if(gdCCheckboxes.get(16).getState()) rt.addValue("Rectangularity", stats.area/arbBox);
        if(gdCCheckboxes.get(18).getState()) rt.addValue("MinR", radiiValues[0]);
        if(gdCCheckboxes.get(17).getState()) rt.addValue("MaxR", radiiValues[1]);
        if(gdCCheckboxes.get(19).getState()) rt.addValue("MeanR", radiiValues[2]);
        if(gdCCheckboxes.get(20).getState()) rt.addValue("VarianceR", radiiValues[3]);
        if(gdCCheckboxes.get(24).getState()) rt.addValue("AreaEquivD", Math.sqrt(4/Math.PI) * stats.area);
        if(gdCCheckboxes.get(25).getState()) rt.addValue("PerEquivD", stats.area/Math.PI);
        if(gdCCheckboxes.get(26).getState()) rt.addValue("EquivEllAr", (Math.PI * feretVector[0] * stats.roiWidth)/4);
        if(gdCCheckboxes.get(34).getState()) rt.addValue("ModRatio", (2 * radiiValues[0])/feretVector[0]);
        if(gdCCheckboxes.get(35).getState()) rt.addValue("Sphericity", radiiValues[0] / radiiValues[1]);// also called radius ratio
        if(gdCCheckboxes.get(36).getState()) rt.addValue("Endocarp", stats.area - perimeter);
        if(gdCCheckboxes.get(42).getState()) rt.addValue("Haralick Ratio", radiiValues[2] / radiiValues[4]);
        if(gdCCheckboxes.get(43).getState()) rt.addValue("Elongation", Math.pow(perimeter, 2)/(4 * Math.PI * stats.area));
        if(gdCCheckboxes.get(44).getState()) rt.addValue("Min Feret", feretVector[2]);

        if(imp.getType() == ImagePlus.GRAY8 || imp.getType() == ImagePlus.GRAY16 || imp.getType() == ImagePlus.GRAY32) {

            if (gdCCheckboxes.get(45).getState()){

                rt.addValue("Entropy", getEntropy(histogram, stats.area));
                rt.addValue("Intensity Sum", getIntensitySum(histogram));
                rt.addValue("Square IntensitySum", getSquareIntensitySum(histogram));
                rt.addValue("Uniformity", getUniformity(histogram, stats.area));
                rt.addValue("Smoothness", getSmoothness(variance));
                rt.addValue("Min gray value", minMaxGray[0]);
                rt.addValue("Max gray value", minMaxGray[1]);
            }

            if (gdCCheckboxes.get(54).getState()) rt.addValue("Entropy", getEntropy(histogram, stats.area));
            if (gdCCheckboxes.get(55).getState()) rt.addValue("Intensity Sum", getIntensitySum(histogram));
            if (gdCCheckboxes.get(56).getState()) rt.addValue("Square IntensitySum", getSquareIntensitySum(histogram));
            if (gdCCheckboxes.get(57).getState()) rt.addValue("Uniformity", getUniformity(histogram, stats.area));
            if (gdCCheckboxes.get(58).getState()) rt.addValue("Smoothness", getSmoothness(variance));
            if (gdCCheckboxes.get(49).getState()){
                rt.addValue("Min gray value", minMaxGray[0]);
                rt.addValue("Max gray value", minMaxGray[1]);
            }
        }
        if (addToManager) {
            if (roiManager==null) {
                if (Macro.getOptions()!=null && Interpreter.isBatchMode())
                    roiManager = Interpreter.getBatchModeRoiManager();
                if (roiManager==null) {
                    Frame frame = WindowManager.getFrame("ROI Manager");
                    if (frame==null)
                        IJ.run("ROI Manager...");
                    frame = WindowManager.getFrame("ROI Manager");
                    if (frame==null || !(frame instanceof RoiManager))
                    {addToManager=false; return;}
                    roiManager = (RoiManager)frame;
                }
                if (resetCounter)
                    roiManager.runCommand("reset");
            }
            if (imp.getStackSize()>1) {
                int n = imp.getCurrentSlice();
                if (hyperstack) {
                    int[] pos = imp.convertIndexToPosition(n);
                    roi.setPosition(pos[0],pos[1],pos[2]);
                } else
                    roi.setPosition(n);
            }
            if (lineWidth!=1)
                roi.setStrokeWidth(lineWidth);
            roiManager.add(imp, roi, rt.size());
        }
        if (showResultsWindow && showResults)
            rt.addResults();
        rt.updateResults();//aggiunto da me
    }

    /** Draws a selected particle in a separate image.  This is
     another method subclasses may want to override. */
    protected void drawParticle(ImageProcessor drawIP, Roi roi,
                                ImageStatistics stats, ImageProcessor mask) {
        switch (showChoice) {
            case MASKS: drawFilledParticle(drawIP, roi, mask); break;
            case OUTLINES: case BARE_OUTLINES: case OVERLAY_OUTLINES: case OVERLAY_MASKS:
                drawOutline(drawIP, roi, rt.size()); break;
            case ELLIPSES: drawEllipse(drawIP, stats, rt.size()); break;
            case ROI_MASKS: drawRoiFilledParticle(drawIP, roi, mask, rt.size()); break;
            default:
        }
    }

    void drawFilledParticle(ImageProcessor ip, Roi roi, ImageProcessor mask) {
        ip.setRoi(roi.getBounds());
        ip.fill(mask);
    }

    void drawOutline(ImageProcessor ip, Roi roi, int count) {
        if (showChoice==OVERLAY_OUTLINES || showChoice==OVERLAY_MASKS) {
            if (overlay==null) {
                overlay = new Overlay();
                overlay.drawLabels(true);
                overlay.setLabelFont(new Font("SansSerif", Font.PLAIN, fontSize));
            }
            Roi roi2 = (Roi)roi.clone();
            roi2.setStrokeColor(Color.cyan);
            if (lineWidth!=1)
                roi2.setStrokeWidth(lineWidth);
            if (showChoice==OVERLAY_MASKS)
                roi2.setFillColor(Color.cyan);
            if (processStack) {
                if (hyperstack) {
                    int[] pos = imp.convertIndexToPosition(slice);
                    roi2.setPosition(pos[0],pos[1],pos[2]);
                } else
                    roi2.setPosition(slice);
            }
            if (showResults)
                roi2.setName(""+count);
            overlay.add(roi2);
        } else {
            Rectangle r = roi.getBounds();
            int nPoints = ((PolygonRoi)roi).getNCoordinates();
            int[] xp = ((PolygonRoi)roi).getXCoordinates();
            int[] yp = ((PolygonRoi)roi).getYCoordinates();
            int x=r.x, y=r.y;
            if (!inSituShow)
                ip.setValue(0.0);
            ip.moveTo(x+xp[0], y+yp[0]);
            for (int i=1; i<nPoints; i++)
                ip.lineTo(x+xp[i], y+yp[i]);
            ip.lineTo(x+xp[0], y+yp[0]);
            if (showChoice!=BARE_OUTLINES) {
                String s = ResultsTable.d2s(count,0);
                ip.moveTo(r.x+r.width/2-ip.getStringWidth(s)/2, r.y+r.height/2+fontSize/2);
                if (!inSituShow)
                    ip.setValue(1.0);
                ip.drawString(s);
            }
        }
    }

    void drawEllipse(ImageProcessor ip, ImageStatistics stats, int count) {
        stats.drawEllipse(ip);
    }

    void drawRoiFilledParticle(ImageProcessor ip, Roi roi, ImageProcessor mask, int count) {
        int grayLevel = (count < 65535) ? count : 65535;
        ip.setValue((double) grayLevel);
        ip.setRoi(roi.getBounds());
        ip.fill(mask);
    }

    void showResults() {
        int count = rt.size();
        if (count==0) return;
        boolean lastSlice = !processStack||slice==imp.getStackSize();
        if ((showChoice==OVERLAY_OUTLINES||showChoice==OVERLAY_MASKS) && count>0 && (!processStack||slice==imp.getStackSize()))
            imp.setOverlay(overlay);
        else if (outlines!=null && lastSlice) {
            String title = imp!=null?imp.getTitle():"Outlines";
            String prefix;
            if (showChoice == MASKS)
                prefix = "Mask of ";
            else if (showChoice == ROI_MASKS)
                prefix = "Count Masks of ";
            else
                prefix = "Drawing of ";
            outlines.update(drawIP);
            outputImage = new ImagePlus(prefix+title, outlines);
            outputImage.setCalibration(imp.getCalibration());
            if (inSituShow) {
                if (imp.getStackSize()==1)
                    Undo.setup(Undo.TRANSFORM, imp);
                ImageStack outputStack = outputImage.getStack();
                if (imp.getStackSize()>1 && outputStack.getSize()==1 && imp.getBitDepth()==8)
                    imp.setProcessor(outputStack.getProcessor(1));
                else
                    imp.setStack(null, outputStack);
            } else if (!hideOutputImage)
                outputImage.show();
        }
        if (showResults && !processStack) {
            if (showResultsWindow && rt.size()>0) {
                TextPanel tp = IJ.getTextPanel();
                if (beginningCount>0 && tp!=null && tp.getLineCount()!=count)
                    rt.show("Results");

            }
            firstParticle = beginningCount;
            lastParticle = Analyzer.getCounter()-1;
        } else
            firstParticle = lastParticle = 0;
        if (showResults && rt.size()==0 ){
            int digits = (int)level1==level1&&(int)level2==level2?0:2;
            String range = IJ.d2s(level1,digits)+"-"+IJ.d2s(level2,digits);
            String assummed = noThreshold?"assumed":"";
            IJ.showMessage("Seeds Analysis Plugin", "No particles were detected. The "+assummed+"\nthreshold ("+range+") may not be correct.");
        }
    }

    /** Returns the "Outlines", "Masks", "Elipses" or "Count Masks" image,
     or null if "Nothing" is selected in the "Show:" menu. */
    public ImagePlus getOutputImage() {
        return outputImage;
    }

    /** Set 'hideOutputImage' true to not display the "Show:" image. */
    public void setHideOutputImage(boolean hideOutputImage) {
        this.hideOutputImage = hideOutputImage;
    }

    /** Sets the size of the font used to label outlines in the next particle analyzer instance. */
    public static void setFontSize(int size) {
        nextFontSize = size;
    }

    /** Sets the color ("blue", "black", etc.) of the font used to label outlines in the next particle analyzer instance. */
    public static void setFontColor(String color) {
        nextFontColor = Colors.decode(color, defaultFontColor);
    }

    /** Sets the outline line width for the next ParticleAnalyzer instance. */
    public static void setLineWidth(int width) {
        nextLineWidth = width;
    }

    /** Sets the RoiManager to be used by the next ParticleAnalyzer
     instance. There is a JavaScript example at
     http://imagej.nih.gov/ij/macros/js/HiddenRoiManager.js
     */
    public static void setRoiManager(RoiManager manager) {
        staticRoiManager = manager;
    }

    /** Sets the ResultsTable to be used by the next
     ParticleAnalyzer instance.  */
    public void setResultsTable(ResultsTable rt) { this.rt = rt; }

    int getColumnID(String name) {
        int id = rt.getFreeColumn(name);
        if (id==ResultsTable.COLUMN_IN_USE)
            id = rt.getColumnIndex(name);
        return id;
    }

    void makeCustomLut() {
        IndexColorModel cm = (IndexColorModel)LookUpTable.createGrayscaleColorModel(false);
        byte[] reds = new byte[256];
        byte[] greens = new byte[256];
        byte[] blues = new byte[256];
        cm.getReds(reds);
        cm.getGreens(greens);
        cm.getBlues(blues);
        reds[1] =(byte)fontColor.getRed();
        greens[1] = (byte)fontColor.getGreen();;
        blues[1] = (byte)fontColor.getBlue();;
        customLut = new IndexColorModel(8, 256, reds, greens, blues);
    }

    /** Called once when ImageJ quits. */
    public static void savePreferences(Properties prefs) {
        prefs.put(OPTIONS, Integer.toString(staticOptions));
    }

}