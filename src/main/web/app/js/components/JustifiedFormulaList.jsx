import React from 'react'
import JustifiedFormula from './JustifiedFormula'

const JustifiedFormulaList = ({ formulas }) => (
  <div>
    { formulas.map((formula, i) =>
      <JustifiedFormula
        key={i}
        {...formula}
      />
    )}
  </div>
)

export default JustifiedFormulaList

