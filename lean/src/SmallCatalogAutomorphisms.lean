import SmallCatalogModel
namespace QGI.SmallCatalog
set_option maxRecDepth 16000 in
theorem allRows : ∀ i : Fin 13, rowsOK (i.val+1)=true := by native_decide
end QGI.SmallCatalog
