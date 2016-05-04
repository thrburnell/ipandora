import React from 'react'
import JustifiedFormula from './JustifiedFormula'

const JustifiedFormulaList = ({ formulas, onFormulaClick, clickable = false }) => (
  <div>
    { formulas.map((formula, i) =>
      <JustifiedFormula
        key={i}
        onFormulaClick={clickable ? onFormulaClick : (_) => {}}
        {...formula}
      />
    )}
  </div>
)

export default JustifiedFormulaList

