import React from 'react'
import Formula from './Formula'

const FormulaList = ({ formulas, onFormulaClick, clickable = false }) => (
  <div>
    { formulas.map((formula, i) =>
      <Formula
        key={i}
        onFormulaClick={clickable ? onFormulaClick : (_) => {}}
        {...formula}
      />
    )}
  </div>
)

export default FormulaList

