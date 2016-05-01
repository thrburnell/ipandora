import { connect } from 'react-redux'
import FormulaList from '../components/FormulaList'

const mapStateToProps = (state) => (
  {
    formulas: state.givens
  }
)

const RGivensList = connect(
  mapStateToProps
)(FormulaList)

export default RGivensList

